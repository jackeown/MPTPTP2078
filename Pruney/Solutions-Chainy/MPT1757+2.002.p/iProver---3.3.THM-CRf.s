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
% DateTime   : Thu Dec  3 12:22:40 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 934 expanded)
%              Number of clauses        :  110 ( 154 expanded)
%              Number of leaves         :   21 ( 369 expanded)
%              Depth                    :   39
%              Number of atoms          : 1422 (14726 expanded)
%              Number of equality atoms :  133 (1075 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f44,plain,(
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

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f45])).

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
    inference(flattening,[],[f55])).

fof(f62,plain,(
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

fof(f61,plain,(
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

fof(f60,plain,(
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

fof(f59,plain,(
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

fof(f58,plain,(
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

fof(f57,plain,
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

fof(f63,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f56,f62,f61,f60,f59,f58,f57])).

fof(f99,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f63])).

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

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f102,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | ~ r1_tmap_1(sK2,sK1,sK3,sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f100,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f63])).

fof(f97,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f63])).

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

fof(f42,plain,(
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

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f110,plain,(
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
    inference(equality_resolution,[],[f84])).

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

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f108,plain,(
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
    inference(equality_resolution,[],[f83])).

fof(f93,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f63])).

fof(f92,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

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

fof(f27,plain,(
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
    inference(flattening,[],[f27])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f89,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f90,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f91,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f95,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f87,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f86,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f88,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f94,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f63])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f109,plain,(
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
    inference(equality_resolution,[],[f85])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f78,plain,(
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

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f79,plain,(
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

fof(f107,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f96,plain,(
    v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f103,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f73,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f101,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | r1_tmap_1(sK2,sK1,sK3,sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3794,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3799,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4362,plain,
    ( r2_hidden(sK6,u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3794,c_3799])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4159,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(X0))
    | ~ r2_hidden(sK6,k1_connsp_2(sK4,sK6))
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4338,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK6,k1_connsp_2(sK4,sK6))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4159])).

cnf(c_4339,plain,
    ( m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK6,k1_connsp_2(sK4,sK6)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4338])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3796,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK5) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_24,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_3882,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3796,c_24])).

cnf(c_52,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f110])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f108])).

cnf(c_204,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_19])).

cnf(c_205,plain,
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
    inference(renaming,[status(thm)],[c_204])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_655,plain,
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
    inference(resolution_lifted,[status(thm)],[c_205,c_31])).

cnf(c_656,plain,
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
    inference(unflattening,[status(thm)],[c_655])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_660,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_656,c_32])).

cnf(c_661,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_660])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_696,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_661,c_10])).

cnf(c_865,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_696])).

cnf(c_866,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_865])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_870,plain,
    ( ~ v2_pre_topc(X0)
    | ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_866,c_35,c_34,c_33,c_29])).

cnf(c_871,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_870])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1327,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_871,c_37])).

cnf(c_1328,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1327])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1332,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1328,c_38,c_36,c_30])).

cnf(c_1333,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1332])).

cnf(c_2231,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1333])).

cnf(c_4046,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2231])).

cnf(c_4047,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4046])).

cnf(c_4055,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3882,c_52,c_4047])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f109])).

cnf(c_14,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_17,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_212,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_18])).

cnf(c_213,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_212])).

cnf(c_28,negated_conjecture,
    ( v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_554,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_213,c_28])).

cnf(c_555,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(c_557,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_555,c_34,c_33,c_27])).

cnf(c_567,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(sK4) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_557])).

cnf(c_568,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,u1_struct_0(sK4))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_572,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_connsp_2(u1_struct_0(sK4),sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_568,c_35,c_34,c_33])).

cnf(c_573,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_572])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_586,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK2,X0)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,u1_struct_0(sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_573,c_6])).

cnf(c_599,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ r2_hidden(X6,u1_struct_0(sK4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | X6 != X3
    | u1_struct_0(sK4) != X5
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_586])).

cnf(c_600,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,X2,X0),X3)
    | r1_tmap_1(sK2,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | ~ r2_hidden(X3,u1_struct_0(sK4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_599])).

cnf(c_604,plain,
    ( ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK2)
    | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
    | r1_tmap_1(sK2,X1,X2,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,X2,X0),X3)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_600,c_35,c_34,c_33])).

cnf(c_605,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,X2,X0),X3)
    | r1_tmap_1(sK2,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | ~ r2_hidden(X3,u1_struct_0(sK4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_604])).

cnf(c_638,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,X2,X0),X3)
    | r1_tmap_1(sK2,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | ~ r2_hidden(X3,u1_struct_0(sK4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_605,c_6])).

cnf(c_761,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,X2,X0),X3)
    | r1_tmap_1(sK2,X1,X2,X3)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | ~ r2_hidden(X3,u1_struct_0(sK4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_638])).

cnf(c_762,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
    | r1_tmap_1(sK2,X1,sK3,X2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | ~ r2_hidden(X2,u1_struct_0(sK4))
    | ~ v1_funct_1(sK3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_761])).

cnf(c_766,plain,
    ( ~ r2_hidden(X2,u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK2)
    | r1_tmap_1(sK2,X1,sK3,X2)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_762,c_32])).

cnf(c_767,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
    | r1_tmap_1(sK2,X1,sK3,X2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | ~ r2_hidden(X2,u1_struct_0(sK4))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_766])).

cnf(c_904,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
    | r1_tmap_1(sK2,X1,sK3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | ~ r2_hidden(X2,u1_struct_0(sK4))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != sK2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_767])).

cnf(c_905,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ r2_hidden(X1,u1_struct_0(sK4))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_904])).

cnf(c_814,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_815,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_814])).

cnf(c_909,plain,
    ( v2_struct_0(X0)
    | ~ r2_hidden(X1,u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_905,c_33,c_29,c_815])).

cnf(c_910,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ r2_hidden(X1,u1_struct_0(sK4))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_909])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_935,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r2_hidden(X1,u1_struct_0(sK4))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_910,c_3])).

cnf(c_1300,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r2_hidden(X1,u1_struct_0(sK4))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_935,c_37])).

cnf(c_1301,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ r2_hidden(X0,u1_struct_0(sK4))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1300])).

cnf(c_1305,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r2_hidden(X0,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1301,c_38,c_36,c_30])).

cnf(c_1306,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1305])).

cnf(c_2235,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,u1_struct_0(sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1306])).

cnf(c_4049,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2235])).

cnf(c_4050,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4049])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_854,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_27])).

cnf(c_855,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_854])).

cnf(c_857,plain,
    ( v2_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_855,c_34,c_33])).

cnf(c_1480,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_857])).

cnf(c_1481,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,k1_connsp_2(sK4,X0))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1480])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_843,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_27])).

cnf(c_844,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_843])).

cnf(c_1485,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,k1_connsp_2(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1481,c_33,c_29,c_844])).

cnf(c_4039,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | r2_hidden(sK6,k1_connsp_2(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_1485])).

cnf(c_4040,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK6,k1_connsp_2(sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4039])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1498,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_857])).

cnf(c_1499,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k1_connsp_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1498])).

cnf(c_1503,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k1_connsp_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1499,c_33,c_29,c_844])).

cnf(c_4036,plain,
    ( m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1503])).

cnf(c_4037,plain,
    ( m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4036])).

cnf(c_23,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,sK3,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3795,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK5) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3865,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3795,c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4362,c_4339,c_4055,c_4050,c_4040,c_4037,c_3865,c_52])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:07:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.20/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/0.98  
% 2.20/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.20/0.98  
% 2.20/0.98  ------  iProver source info
% 2.20/0.98  
% 2.20/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.20/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.20/0.98  git: non_committed_changes: false
% 2.20/0.98  git: last_make_outside_of_git: false
% 2.20/0.98  
% 2.20/0.98  ------ 
% 2.20/0.98  
% 2.20/0.98  ------ Input Options
% 2.20/0.98  
% 2.20/0.98  --out_options                           all
% 2.20/0.98  --tptp_safe_out                         true
% 2.20/0.98  --problem_path                          ""
% 2.20/0.98  --include_path                          ""
% 2.20/0.98  --clausifier                            res/vclausify_rel
% 2.20/0.98  --clausifier_options                    --mode clausify
% 2.20/0.98  --stdin                                 false
% 2.20/0.98  --stats_out                             all
% 2.20/0.98  
% 2.20/0.98  ------ General Options
% 2.20/0.98  
% 2.20/0.98  --fof                                   false
% 2.20/0.98  --time_out_real                         305.
% 2.20/0.98  --time_out_virtual                      -1.
% 2.20/0.98  --symbol_type_check                     false
% 2.20/0.98  --clausify_out                          false
% 2.20/0.98  --sig_cnt_out                           false
% 2.20/0.98  --trig_cnt_out                          false
% 2.20/0.98  --trig_cnt_out_tolerance                1.
% 2.20/0.98  --trig_cnt_out_sk_spl                   false
% 2.20/0.98  --abstr_cl_out                          false
% 2.20/0.98  
% 2.20/0.98  ------ Global Options
% 2.20/0.98  
% 2.20/0.98  --schedule                              default
% 2.20/0.98  --add_important_lit                     false
% 2.20/0.98  --prop_solver_per_cl                    1000
% 2.20/0.98  --min_unsat_core                        false
% 2.20/0.98  --soft_assumptions                      false
% 2.20/0.98  --soft_lemma_size                       3
% 2.20/0.98  --prop_impl_unit_size                   0
% 2.20/0.98  --prop_impl_unit                        []
% 2.20/0.98  --share_sel_clauses                     true
% 2.20/0.98  --reset_solvers                         false
% 2.20/0.98  --bc_imp_inh                            [conj_cone]
% 2.20/0.98  --conj_cone_tolerance                   3.
% 2.20/0.98  --extra_neg_conj                        none
% 2.20/0.98  --large_theory_mode                     true
% 2.20/0.98  --prolific_symb_bound                   200
% 2.20/0.98  --lt_threshold                          2000
% 2.20/0.98  --clause_weak_htbl                      true
% 2.20/0.98  --gc_record_bc_elim                     false
% 2.20/0.98  
% 2.20/0.98  ------ Preprocessing Options
% 2.20/0.98  
% 2.20/0.98  --preprocessing_flag                    true
% 2.20/0.98  --time_out_prep_mult                    0.1
% 2.20/0.98  --splitting_mode                        input
% 2.20/0.98  --splitting_grd                         true
% 2.20/0.98  --splitting_cvd                         false
% 2.20/0.98  --splitting_cvd_svl                     false
% 2.20/0.98  --splitting_nvd                         32
% 2.20/0.98  --sub_typing                            true
% 2.20/0.98  --prep_gs_sim                           true
% 2.20/0.98  --prep_unflatten                        true
% 2.20/0.98  --prep_res_sim                          true
% 2.20/0.98  --prep_upred                            true
% 2.20/0.98  --prep_sem_filter                       exhaustive
% 2.20/0.98  --prep_sem_filter_out                   false
% 2.20/0.98  --pred_elim                             true
% 2.20/0.98  --res_sim_input                         true
% 2.20/0.98  --eq_ax_congr_red                       true
% 2.20/0.98  --pure_diseq_elim                       true
% 2.20/0.98  --brand_transform                       false
% 2.20/0.98  --non_eq_to_eq                          false
% 2.20/0.98  --prep_def_merge                        true
% 2.20/0.98  --prep_def_merge_prop_impl              false
% 2.20/0.98  --prep_def_merge_mbd                    true
% 2.20/0.98  --prep_def_merge_tr_red                 false
% 2.20/0.98  --prep_def_merge_tr_cl                  false
% 2.20/0.98  --smt_preprocessing                     true
% 2.20/0.98  --smt_ac_axioms                         fast
% 2.20/0.98  --preprocessed_out                      false
% 2.20/0.98  --preprocessed_stats                    false
% 2.20/0.98  
% 2.20/0.98  ------ Abstraction refinement Options
% 2.20/0.98  
% 2.20/0.98  --abstr_ref                             []
% 2.20/0.98  --abstr_ref_prep                        false
% 2.20/0.98  --abstr_ref_until_sat                   false
% 2.20/0.98  --abstr_ref_sig_restrict                funpre
% 2.20/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.20/0.98  --abstr_ref_under                       []
% 2.20/0.98  
% 2.20/0.98  ------ SAT Options
% 2.20/0.98  
% 2.20/0.98  --sat_mode                              false
% 2.20/0.98  --sat_fm_restart_options                ""
% 2.20/0.98  --sat_gr_def                            false
% 2.20/0.98  --sat_epr_types                         true
% 2.20/0.98  --sat_non_cyclic_types                  false
% 2.20/0.98  --sat_finite_models                     false
% 2.20/0.98  --sat_fm_lemmas                         false
% 2.20/0.98  --sat_fm_prep                           false
% 2.20/0.98  --sat_fm_uc_incr                        true
% 2.20/0.98  --sat_out_model                         small
% 2.20/0.98  --sat_out_clauses                       false
% 2.20/0.98  
% 2.20/0.98  ------ QBF Options
% 2.20/0.98  
% 2.20/0.98  --qbf_mode                              false
% 2.20/0.98  --qbf_elim_univ                         false
% 2.20/0.98  --qbf_dom_inst                          none
% 2.20/0.98  --qbf_dom_pre_inst                      false
% 2.20/0.98  --qbf_sk_in                             false
% 2.20/0.98  --qbf_pred_elim                         true
% 2.20/0.98  --qbf_split                             512
% 2.20/0.98  
% 2.20/0.98  ------ BMC1 Options
% 2.20/0.98  
% 2.20/0.98  --bmc1_incremental                      false
% 2.20/0.98  --bmc1_axioms                           reachable_all
% 2.20/0.98  --bmc1_min_bound                        0
% 2.20/0.98  --bmc1_max_bound                        -1
% 2.20/0.98  --bmc1_max_bound_default                -1
% 2.20/0.98  --bmc1_symbol_reachability              true
% 2.20/0.98  --bmc1_property_lemmas                  false
% 2.20/0.98  --bmc1_k_induction                      false
% 2.20/0.98  --bmc1_non_equiv_states                 false
% 2.20/0.98  --bmc1_deadlock                         false
% 2.20/0.98  --bmc1_ucm                              false
% 2.20/0.98  --bmc1_add_unsat_core                   none
% 2.20/0.98  --bmc1_unsat_core_children              false
% 2.20/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.20/0.98  --bmc1_out_stat                         full
% 2.20/0.98  --bmc1_ground_init                      false
% 2.20/0.98  --bmc1_pre_inst_next_state              false
% 2.20/0.98  --bmc1_pre_inst_state                   false
% 2.20/0.98  --bmc1_pre_inst_reach_state             false
% 2.20/0.98  --bmc1_out_unsat_core                   false
% 2.20/0.98  --bmc1_aig_witness_out                  false
% 2.20/0.98  --bmc1_verbose                          false
% 2.20/0.98  --bmc1_dump_clauses_tptp                false
% 2.20/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.20/0.98  --bmc1_dump_file                        -
% 2.20/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.20/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.20/0.98  --bmc1_ucm_extend_mode                  1
% 2.20/0.98  --bmc1_ucm_init_mode                    2
% 2.20/0.98  --bmc1_ucm_cone_mode                    none
% 2.20/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.20/0.98  --bmc1_ucm_relax_model                  4
% 2.20/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.20/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.20/0.98  --bmc1_ucm_layered_model                none
% 2.20/0.98  --bmc1_ucm_max_lemma_size               10
% 2.20/0.98  
% 2.20/0.98  ------ AIG Options
% 2.20/0.98  
% 2.20/0.98  --aig_mode                              false
% 2.20/0.98  
% 2.20/0.98  ------ Instantiation Options
% 2.20/0.98  
% 2.20/0.98  --instantiation_flag                    true
% 2.20/0.98  --inst_sos_flag                         false
% 2.20/0.98  --inst_sos_phase                        true
% 2.20/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.20/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.20/0.98  --inst_lit_sel_side                     num_symb
% 2.20/0.98  --inst_solver_per_active                1400
% 2.20/0.98  --inst_solver_calls_frac                1.
% 2.20/0.98  --inst_passive_queue_type               priority_queues
% 2.20/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.20/0.98  --inst_passive_queues_freq              [25;2]
% 2.20/0.98  --inst_dismatching                      true
% 2.20/0.98  --inst_eager_unprocessed_to_passive     true
% 2.20/0.98  --inst_prop_sim_given                   true
% 2.20/0.98  --inst_prop_sim_new                     false
% 2.20/0.98  --inst_subs_new                         false
% 2.20/0.98  --inst_eq_res_simp                      false
% 2.20/0.98  --inst_subs_given                       false
% 2.20/0.98  --inst_orphan_elimination               true
% 2.20/0.98  --inst_learning_loop_flag               true
% 2.20/0.98  --inst_learning_start                   3000
% 2.20/0.98  --inst_learning_factor                  2
% 2.20/0.98  --inst_start_prop_sim_after_learn       3
% 2.20/0.98  --inst_sel_renew                        solver
% 2.20/0.98  --inst_lit_activity_flag                true
% 2.20/0.98  --inst_restr_to_given                   false
% 2.20/0.98  --inst_activity_threshold               500
% 2.20/0.98  --inst_out_proof                        true
% 2.20/0.98  
% 2.20/0.98  ------ Resolution Options
% 2.20/0.98  
% 2.20/0.98  --resolution_flag                       true
% 2.20/0.98  --res_lit_sel                           adaptive
% 2.20/0.98  --res_lit_sel_side                      none
% 2.20/0.98  --res_ordering                          kbo
% 2.20/0.98  --res_to_prop_solver                    active
% 2.20/0.98  --res_prop_simpl_new                    false
% 2.20/0.98  --res_prop_simpl_given                  true
% 2.20/0.98  --res_passive_queue_type                priority_queues
% 2.20/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.20/0.98  --res_passive_queues_freq               [15;5]
% 2.20/0.98  --res_forward_subs                      full
% 2.20/0.98  --res_backward_subs                     full
% 2.20/0.98  --res_forward_subs_resolution           true
% 2.20/0.98  --res_backward_subs_resolution          true
% 2.20/0.98  --res_orphan_elimination                true
% 2.20/0.98  --res_time_limit                        2.
% 2.20/0.98  --res_out_proof                         true
% 2.20/0.98  
% 2.20/0.98  ------ Superposition Options
% 2.20/0.98  
% 2.20/0.98  --superposition_flag                    true
% 2.20/0.98  --sup_passive_queue_type                priority_queues
% 2.20/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.20/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.20/0.98  --demod_completeness_check              fast
% 2.20/0.98  --demod_use_ground                      true
% 2.20/0.98  --sup_to_prop_solver                    passive
% 2.20/0.98  --sup_prop_simpl_new                    true
% 2.20/0.98  --sup_prop_simpl_given                  true
% 2.20/0.98  --sup_fun_splitting                     false
% 2.20/0.98  --sup_smt_interval                      50000
% 2.20/0.98  
% 2.20/0.98  ------ Superposition Simplification Setup
% 2.20/0.98  
% 2.20/0.98  --sup_indices_passive                   []
% 2.20/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.20/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/0.98  --sup_full_bw                           [BwDemod]
% 2.20/0.98  --sup_immed_triv                        [TrivRules]
% 2.20/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.20/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/0.98  --sup_immed_bw_main                     []
% 2.20/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.20/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/0.98  
% 2.20/0.98  ------ Combination Options
% 2.20/0.98  
% 2.20/0.98  --comb_res_mult                         3
% 2.20/0.98  --comb_sup_mult                         2
% 2.20/0.98  --comb_inst_mult                        10
% 2.20/0.98  
% 2.20/0.98  ------ Debug Options
% 2.20/0.98  
% 2.20/0.98  --dbg_backtrace                         false
% 2.20/0.98  --dbg_dump_prop_clauses                 false
% 2.20/0.98  --dbg_dump_prop_clauses_file            -
% 2.20/0.98  --dbg_out_stat                          false
% 2.20/0.98  ------ Parsing...
% 2.20/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.20/0.98  
% 2.20/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.20/0.98  
% 2.20/0.98  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.20/0.98  
% 2.20/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.20/0.98  ------ Proving...
% 2.20/0.98  ------ Problem Properties 
% 2.20/0.98  
% 2.20/0.98  
% 2.20/0.98  clauses                                 31
% 2.20/0.98  conjectures                             6
% 2.20/0.98  EPR                                     5
% 2.20/0.98  Horn                                    28
% 2.20/0.98  unary                                   6
% 2.20/0.98  binary                                  11
% 2.20/0.98  lits                                    77
% 2.20/0.98  lits eq                                 6
% 2.20/0.98  fd_pure                                 0
% 2.20/0.98  fd_pseudo                               0
% 2.20/0.98  fd_cond                                 0
% 2.20/0.98  fd_pseudo_cond                          1
% 2.20/0.98  AC symbols                              0
% 2.20/0.98  
% 2.20/0.98  ------ Schedule dynamic 5 is on 
% 2.20/0.98  
% 2.20/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.20/0.98  
% 2.20/0.98  
% 2.20/0.98  ------ 
% 2.20/0.98  Current options:
% 2.20/0.98  ------ 
% 2.20/0.98  
% 2.20/0.98  ------ Input Options
% 2.20/0.98  
% 2.20/0.98  --out_options                           all
% 2.20/0.98  --tptp_safe_out                         true
% 2.20/0.98  --problem_path                          ""
% 2.20/0.98  --include_path                          ""
% 2.20/0.98  --clausifier                            res/vclausify_rel
% 2.20/0.98  --clausifier_options                    --mode clausify
% 2.20/0.98  --stdin                                 false
% 2.20/0.98  --stats_out                             all
% 2.20/0.98  
% 2.20/0.98  ------ General Options
% 2.20/0.98  
% 2.20/0.98  --fof                                   false
% 2.20/0.98  --time_out_real                         305.
% 2.20/0.98  --time_out_virtual                      -1.
% 2.20/0.98  --symbol_type_check                     false
% 2.20/0.98  --clausify_out                          false
% 2.20/0.98  --sig_cnt_out                           false
% 2.20/0.98  --trig_cnt_out                          false
% 2.20/0.98  --trig_cnt_out_tolerance                1.
% 2.20/0.98  --trig_cnt_out_sk_spl                   false
% 2.20/0.98  --abstr_cl_out                          false
% 2.20/0.98  
% 2.20/0.98  ------ Global Options
% 2.20/0.98  
% 2.20/0.98  --schedule                              default
% 2.20/0.98  --add_important_lit                     false
% 2.20/0.98  --prop_solver_per_cl                    1000
% 2.20/0.98  --min_unsat_core                        false
% 2.20/0.98  --soft_assumptions                      false
% 2.20/0.98  --soft_lemma_size                       3
% 2.20/0.98  --prop_impl_unit_size                   0
% 2.20/0.98  --prop_impl_unit                        []
% 2.20/0.98  --share_sel_clauses                     true
% 2.20/0.98  --reset_solvers                         false
% 2.20/0.98  --bc_imp_inh                            [conj_cone]
% 2.20/0.98  --conj_cone_tolerance                   3.
% 2.20/0.98  --extra_neg_conj                        none
% 2.20/0.98  --large_theory_mode                     true
% 2.20/0.98  --prolific_symb_bound                   200
% 2.20/0.98  --lt_threshold                          2000
% 2.20/0.98  --clause_weak_htbl                      true
% 2.20/0.98  --gc_record_bc_elim                     false
% 2.20/0.98  
% 2.20/0.98  ------ Preprocessing Options
% 2.20/0.98  
% 2.20/0.98  --preprocessing_flag                    true
% 2.20/0.98  --time_out_prep_mult                    0.1
% 2.20/0.98  --splitting_mode                        input
% 2.20/0.98  --splitting_grd                         true
% 2.20/0.98  --splitting_cvd                         false
% 2.20/0.98  --splitting_cvd_svl                     false
% 2.20/0.98  --splitting_nvd                         32
% 2.20/0.98  --sub_typing                            true
% 2.20/0.98  --prep_gs_sim                           true
% 2.20/0.98  --prep_unflatten                        true
% 2.20/0.98  --prep_res_sim                          true
% 2.20/0.98  --prep_upred                            true
% 2.20/0.98  --prep_sem_filter                       exhaustive
% 2.20/0.98  --prep_sem_filter_out                   false
% 2.20/0.98  --pred_elim                             true
% 2.20/0.98  --res_sim_input                         true
% 2.20/0.98  --eq_ax_congr_red                       true
% 2.20/0.98  --pure_diseq_elim                       true
% 2.20/0.98  --brand_transform                       false
% 2.20/0.98  --non_eq_to_eq                          false
% 2.20/0.98  --prep_def_merge                        true
% 2.20/0.98  --prep_def_merge_prop_impl              false
% 2.20/0.98  --prep_def_merge_mbd                    true
% 2.20/0.98  --prep_def_merge_tr_red                 false
% 2.20/0.98  --prep_def_merge_tr_cl                  false
% 2.20/0.98  --smt_preprocessing                     true
% 2.20/0.98  --smt_ac_axioms                         fast
% 2.20/0.98  --preprocessed_out                      false
% 2.20/0.98  --preprocessed_stats                    false
% 2.20/0.98  
% 2.20/0.98  ------ Abstraction refinement Options
% 2.20/0.98  
% 2.20/0.98  --abstr_ref                             []
% 2.20/0.98  --abstr_ref_prep                        false
% 2.20/0.98  --abstr_ref_until_sat                   false
% 2.20/0.98  --abstr_ref_sig_restrict                funpre
% 2.20/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.20/0.98  --abstr_ref_under                       []
% 2.20/0.98  
% 2.20/0.98  ------ SAT Options
% 2.20/0.98  
% 2.20/0.98  --sat_mode                              false
% 2.20/0.98  --sat_fm_restart_options                ""
% 2.20/0.98  --sat_gr_def                            false
% 2.20/0.98  --sat_epr_types                         true
% 2.20/0.98  --sat_non_cyclic_types                  false
% 2.20/0.98  --sat_finite_models                     false
% 2.20/0.98  --sat_fm_lemmas                         false
% 2.20/0.98  --sat_fm_prep                           false
% 2.20/0.98  --sat_fm_uc_incr                        true
% 2.20/0.98  --sat_out_model                         small
% 2.20/0.98  --sat_out_clauses                       false
% 2.20/0.98  
% 2.20/0.98  ------ QBF Options
% 2.20/0.98  
% 2.20/0.98  --qbf_mode                              false
% 2.20/0.98  --qbf_elim_univ                         false
% 2.20/0.98  --qbf_dom_inst                          none
% 2.20/0.98  --qbf_dom_pre_inst                      false
% 2.20/0.98  --qbf_sk_in                             false
% 2.20/0.98  --qbf_pred_elim                         true
% 2.20/0.98  --qbf_split                             512
% 2.20/0.98  
% 2.20/0.98  ------ BMC1 Options
% 2.20/0.98  
% 2.20/0.98  --bmc1_incremental                      false
% 2.20/0.98  --bmc1_axioms                           reachable_all
% 2.20/0.98  --bmc1_min_bound                        0
% 2.20/0.98  --bmc1_max_bound                        -1
% 2.20/0.98  --bmc1_max_bound_default                -1
% 2.20/0.98  --bmc1_symbol_reachability              true
% 2.20/0.98  --bmc1_property_lemmas                  false
% 2.20/0.98  --bmc1_k_induction                      false
% 2.20/0.98  --bmc1_non_equiv_states                 false
% 2.20/0.98  --bmc1_deadlock                         false
% 2.20/0.98  --bmc1_ucm                              false
% 2.20/0.98  --bmc1_add_unsat_core                   none
% 2.20/0.98  --bmc1_unsat_core_children              false
% 2.20/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.20/0.98  --bmc1_out_stat                         full
% 2.20/0.98  --bmc1_ground_init                      false
% 2.20/0.98  --bmc1_pre_inst_next_state              false
% 2.20/0.98  --bmc1_pre_inst_state                   false
% 2.20/0.98  --bmc1_pre_inst_reach_state             false
% 2.20/0.98  --bmc1_out_unsat_core                   false
% 2.20/0.98  --bmc1_aig_witness_out                  false
% 2.20/0.98  --bmc1_verbose                          false
% 2.20/0.98  --bmc1_dump_clauses_tptp                false
% 2.20/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.20/0.98  --bmc1_dump_file                        -
% 2.20/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.20/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.20/0.98  --bmc1_ucm_extend_mode                  1
% 2.20/0.98  --bmc1_ucm_init_mode                    2
% 2.20/0.98  --bmc1_ucm_cone_mode                    none
% 2.20/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.20/0.98  --bmc1_ucm_relax_model                  4
% 2.20/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.20/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.20/0.98  --bmc1_ucm_layered_model                none
% 2.20/0.98  --bmc1_ucm_max_lemma_size               10
% 2.20/0.98  
% 2.20/0.98  ------ AIG Options
% 2.20/0.98  
% 2.20/0.98  --aig_mode                              false
% 2.20/0.98  
% 2.20/0.98  ------ Instantiation Options
% 2.20/0.98  
% 2.20/0.98  --instantiation_flag                    true
% 2.20/0.98  --inst_sos_flag                         false
% 2.20/0.98  --inst_sos_phase                        true
% 2.20/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.20/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.20/0.98  --inst_lit_sel_side                     none
% 2.20/0.98  --inst_solver_per_active                1400
% 2.20/0.98  --inst_solver_calls_frac                1.
% 2.20/0.98  --inst_passive_queue_type               priority_queues
% 2.20/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.20/0.98  --inst_passive_queues_freq              [25;2]
% 2.20/0.98  --inst_dismatching                      true
% 2.20/0.98  --inst_eager_unprocessed_to_passive     true
% 2.20/0.98  --inst_prop_sim_given                   true
% 2.20/0.98  --inst_prop_sim_new                     false
% 2.20/0.98  --inst_subs_new                         false
% 2.20/0.98  --inst_eq_res_simp                      false
% 2.20/0.98  --inst_subs_given                       false
% 2.20/0.98  --inst_orphan_elimination               true
% 2.20/0.98  --inst_learning_loop_flag               true
% 2.20/0.98  --inst_learning_start                   3000
% 2.20/0.98  --inst_learning_factor                  2
% 2.20/0.98  --inst_start_prop_sim_after_learn       3
% 2.20/0.98  --inst_sel_renew                        solver
% 2.20/0.98  --inst_lit_activity_flag                true
% 2.20/0.98  --inst_restr_to_given                   false
% 2.20/0.98  --inst_activity_threshold               500
% 2.20/0.98  --inst_out_proof                        true
% 2.20/0.98  
% 2.20/0.98  ------ Resolution Options
% 2.20/0.98  
% 2.20/0.98  --resolution_flag                       false
% 2.20/0.98  --res_lit_sel                           adaptive
% 2.20/0.98  --res_lit_sel_side                      none
% 2.20/0.98  --res_ordering                          kbo
% 2.20/0.98  --res_to_prop_solver                    active
% 2.20/0.98  --res_prop_simpl_new                    false
% 2.20/0.98  --res_prop_simpl_given                  true
% 2.20/0.98  --res_passive_queue_type                priority_queues
% 2.20/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.20/0.98  --res_passive_queues_freq               [15;5]
% 2.20/0.98  --res_forward_subs                      full
% 2.20/0.98  --res_backward_subs                     full
% 2.20/0.98  --res_forward_subs_resolution           true
% 2.20/0.98  --res_backward_subs_resolution          true
% 2.20/0.98  --res_orphan_elimination                true
% 2.20/0.98  --res_time_limit                        2.
% 2.20/0.98  --res_out_proof                         true
% 2.20/0.98  
% 2.20/0.98  ------ Superposition Options
% 2.20/0.98  
% 2.20/0.98  --superposition_flag                    true
% 2.20/0.98  --sup_passive_queue_type                priority_queues
% 2.20/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.20/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.20/0.98  --demod_completeness_check              fast
% 2.20/0.98  --demod_use_ground                      true
% 2.20/0.98  --sup_to_prop_solver                    passive
% 2.20/0.98  --sup_prop_simpl_new                    true
% 2.20/0.98  --sup_prop_simpl_given                  true
% 2.20/0.98  --sup_fun_splitting                     false
% 2.20/0.98  --sup_smt_interval                      50000
% 2.20/0.98  
% 2.20/0.98  ------ Superposition Simplification Setup
% 2.20/0.98  
% 2.20/0.98  --sup_indices_passive                   []
% 2.20/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.20/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/0.98  --sup_full_bw                           [BwDemod]
% 2.20/0.98  --sup_immed_triv                        [TrivRules]
% 2.20/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.20/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/0.98  --sup_immed_bw_main                     []
% 2.20/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.20/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/0.98  
% 2.20/0.98  ------ Combination Options
% 2.20/0.98  
% 2.20/0.98  --comb_res_mult                         3
% 2.20/0.98  --comb_sup_mult                         2
% 2.20/0.98  --comb_inst_mult                        10
% 2.20/0.98  
% 2.20/0.98  ------ Debug Options
% 2.20/0.98  
% 2.20/0.98  --dbg_backtrace                         false
% 2.20/0.98  --dbg_dump_prop_clauses                 false
% 2.20/0.98  --dbg_dump_prop_clauses_file            -
% 2.20/0.98  --dbg_out_stat                          false
% 2.20/0.98  
% 2.20/0.98  
% 2.20/0.98  
% 2.20/0.98  
% 2.20/0.98  ------ Proving...
% 2.20/0.98  
% 2.20/0.98  
% 2.20/0.98  % SZS status Theorem for theBenchmark.p
% 2.20/0.98  
% 2.20/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.20/0.98  
% 2.20/0.98  fof(f17,conjecture,(
% 2.20/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f18,negated_conjecture,(
% 2.20/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.20/0.98    inference(negated_conjecture,[],[f17])).
% 2.20/0.98  
% 2.20/0.98  fof(f44,plain,(
% 2.20/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.20/0.98    inference(ennf_transformation,[],[f18])).
% 2.20/0.98  
% 2.20/0.98  fof(f45,plain,(
% 2.20/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.20/0.98    inference(flattening,[],[f44])).
% 2.20/0.98  
% 2.20/0.98  fof(f55,plain,(
% 2.20/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.20/0.98    inference(nnf_transformation,[],[f45])).
% 2.20/0.98  
% 2.20/0.98  fof(f56,plain,(
% 2.20/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.20/0.98    inference(flattening,[],[f55])).
% 2.20/0.98  
% 2.20/0.98  fof(f62,plain,(
% 2.20/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6) | r1_tmap_1(X1,X0,X2,X4)) & sK6 = X4 & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.20/0.98    introduced(choice_axiom,[])).
% 2.20/0.98  
% 2.20/0.98  fof(f61,plain,(
% 2.20/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK5)) & sK5 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK5,u1_struct_0(X1)))) )),
% 2.20/0.98    introduced(choice_axiom,[])).
% 2.20/0.98  
% 2.20/0.98  fof(f60,plain,(
% 2.20/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK4,X1) & v1_tsep_1(sK4,X1) & ~v2_struct_0(sK4))) )),
% 2.20/0.98    introduced(choice_axiom,[])).
% 2.20/0.98  
% 2.20/0.98  fof(f59,plain,(
% 2.20/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X5) | ~r1_tmap_1(X1,X0,sK3,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X5) | r1_tmap_1(X1,X0,sK3,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 2.20/0.98    introduced(choice_axiom,[])).
% 2.20/0.98  
% 2.20/0.98  fof(f58,plain,(
% 2.20/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X5) | ~r1_tmap_1(sK2,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X5) | r1_tmap_1(sK2,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK2))) & m1_pre_topc(X3,sK2) & v1_tsep_1(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.20/0.98    introduced(choice_axiom,[])).
% 2.20/0.98  
% 2.20/0.98  fof(f57,plain,(
% 2.20/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X5) | ~r1_tmap_1(X1,sK1,X2,X4)) & (r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X5) | r1_tmap_1(X1,sK1,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.20/0.98    introduced(choice_axiom,[])).
% 2.20/0.98  
% 2.20/0.98  fof(f63,plain,(
% 2.20/0.98    ((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | ~r1_tmap_1(sK2,sK1,sK3,sK5)) & (r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | r1_tmap_1(sK2,sK1,sK3,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK2))) & m1_pre_topc(sK4,sK2) & v1_tsep_1(sK4,sK2) & ~v2_struct_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.20/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f56,f62,f61,f60,f59,f58,f57])).
% 2.20/0.98  
% 2.20/0.98  fof(f99,plain,(
% 2.20/0.98    m1_subset_1(sK6,u1_struct_0(sK4))),
% 2.20/0.98    inference(cnf_transformation,[],[f63])).
% 2.20/0.98  
% 2.20/0.98  fof(f3,axiom,(
% 2.20/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f19,plain,(
% 2.20/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.20/0.98    inference(ennf_transformation,[],[f3])).
% 2.20/0.98  
% 2.20/0.98  fof(f20,plain,(
% 2.20/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.20/0.98    inference(flattening,[],[f19])).
% 2.20/0.98  
% 2.20/0.98  fof(f69,plain,(
% 2.20/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f20])).
% 2.20/0.98  
% 2.20/0.98  fof(f5,axiom,(
% 2.20/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f23,plain,(
% 2.20/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.20/0.98    inference(ennf_transformation,[],[f5])).
% 2.20/0.98  
% 2.20/0.98  fof(f71,plain,(
% 2.20/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f23])).
% 2.20/0.98  
% 2.20/0.98  fof(f102,plain,(
% 2.20/0.98    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | ~r1_tmap_1(sK2,sK1,sK3,sK5)),
% 2.20/0.98    inference(cnf_transformation,[],[f63])).
% 2.20/0.98  
% 2.20/0.98  fof(f100,plain,(
% 2.20/0.98    sK5 = sK6),
% 2.20/0.98    inference(cnf_transformation,[],[f63])).
% 2.20/0.98  
% 2.20/0.98  fof(f97,plain,(
% 2.20/0.98    m1_pre_topc(sK4,sK2)),
% 2.20/0.98    inference(cnf_transformation,[],[f63])).
% 2.20/0.98  
% 2.20/0.98  fof(f16,axiom,(
% 2.20/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f42,plain,(
% 2.20/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.20/0.98    inference(ennf_transformation,[],[f16])).
% 2.20/0.98  
% 2.20/0.98  fof(f43,plain,(
% 2.20/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/0.98    inference(flattening,[],[f42])).
% 2.20/0.98  
% 2.20/0.98  fof(f54,plain,(
% 2.20/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/0.98    inference(nnf_transformation,[],[f43])).
% 2.20/0.98  
% 2.20/0.98  fof(f84,plain,(
% 2.20/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f54])).
% 2.20/0.98  
% 2.20/0.98  fof(f110,plain,(
% 2.20/0.98    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.98    inference(equality_resolution,[],[f84])).
% 2.20/0.98  
% 2.20/0.98  fof(f15,axiom,(
% 2.20/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f40,plain,(
% 2.20/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.20/0.98    inference(ennf_transformation,[],[f15])).
% 2.20/0.98  
% 2.20/0.98  fof(f41,plain,(
% 2.20/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/0.98    inference(flattening,[],[f40])).
% 2.20/0.98  
% 2.20/0.98  fof(f83,plain,(
% 2.20/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f41])).
% 2.20/0.98  
% 2.20/0.98  fof(f108,plain,(
% 2.20/0.98    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.98    inference(equality_resolution,[],[f83])).
% 2.20/0.98  
% 2.20/0.98  fof(f93,plain,(
% 2.20/0.98    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.20/0.98    inference(cnf_transformation,[],[f63])).
% 2.20/0.98  
% 2.20/0.98  fof(f92,plain,(
% 2.20/0.98    v1_funct_1(sK3)),
% 2.20/0.98    inference(cnf_transformation,[],[f63])).
% 2.20/0.98  
% 2.20/0.98  fof(f8,axiom,(
% 2.20/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f27,plain,(
% 2.20/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.20/0.98    inference(ennf_transformation,[],[f8])).
% 2.20/0.98  
% 2.20/0.98  fof(f28,plain,(
% 2.20/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/0.98    inference(flattening,[],[f27])).
% 2.20/0.98  
% 2.20/0.98  fof(f74,plain,(
% 2.20/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f28])).
% 2.20/0.98  
% 2.20/0.98  fof(f89,plain,(
% 2.20/0.98    ~v2_struct_0(sK2)),
% 2.20/0.98    inference(cnf_transformation,[],[f63])).
% 2.20/0.98  
% 2.20/0.98  fof(f90,plain,(
% 2.20/0.98    v2_pre_topc(sK2)),
% 2.20/0.98    inference(cnf_transformation,[],[f63])).
% 2.20/0.98  
% 2.20/0.98  fof(f91,plain,(
% 2.20/0.98    l1_pre_topc(sK2)),
% 2.20/0.98    inference(cnf_transformation,[],[f63])).
% 2.20/0.98  
% 2.20/0.98  fof(f95,plain,(
% 2.20/0.98    ~v2_struct_0(sK4)),
% 2.20/0.98    inference(cnf_transformation,[],[f63])).
% 2.20/0.98  
% 2.20/0.98  fof(f87,plain,(
% 2.20/0.98    v2_pre_topc(sK1)),
% 2.20/0.98    inference(cnf_transformation,[],[f63])).
% 2.20/0.98  
% 2.20/0.98  fof(f86,plain,(
% 2.20/0.98    ~v2_struct_0(sK1)),
% 2.20/0.98    inference(cnf_transformation,[],[f63])).
% 2.20/0.98  
% 2.20/0.98  fof(f88,plain,(
% 2.20/0.98    l1_pre_topc(sK1)),
% 2.20/0.98    inference(cnf_transformation,[],[f63])).
% 2.20/0.98  
% 2.20/0.98  fof(f94,plain,(
% 2.20/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.20/0.98    inference(cnf_transformation,[],[f63])).
% 2.20/0.98  
% 2.20/0.98  fof(f85,plain,(
% 2.20/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f54])).
% 2.20/0.98  
% 2.20/0.98  fof(f109,plain,(
% 2.20/0.98    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.98    inference(equality_resolution,[],[f85])).
% 2.20/0.98  
% 2.20/0.98  fof(f12,axiom,(
% 2.20/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 2.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f35,plain,(
% 2.20/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.20/0.98    inference(ennf_transformation,[],[f12])).
% 2.20/0.98  
% 2.20/0.98  fof(f36,plain,(
% 2.20/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/0.98    inference(flattening,[],[f35])).
% 2.20/0.98  
% 2.20/0.98  fof(f78,plain,(
% 2.20/0.98    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f36])).
% 2.20/0.98  
% 2.20/0.98  fof(f13,axiom,(
% 2.20/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f37,plain,(
% 2.20/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.20/0.98    inference(ennf_transformation,[],[f13])).
% 2.20/0.98  
% 2.20/0.98  fof(f38,plain,(
% 2.20/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.20/0.98    inference(flattening,[],[f37])).
% 2.20/0.98  
% 2.20/0.98  fof(f52,plain,(
% 2.20/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.20/0.98    inference(nnf_transformation,[],[f38])).
% 2.20/0.98  
% 2.20/0.98  fof(f53,plain,(
% 2.20/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.20/0.98    inference(flattening,[],[f52])).
% 2.20/0.98  
% 2.20/0.98  fof(f79,plain,(
% 2.20/0.98    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f53])).
% 2.20/0.98  
% 2.20/0.98  fof(f107,plain,(
% 2.20/0.98    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/0.98    inference(equality_resolution,[],[f79])).
% 2.20/0.98  
% 2.20/0.98  fof(f14,axiom,(
% 2.20/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f39,plain,(
% 2.20/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.20/0.98    inference(ennf_transformation,[],[f14])).
% 2.20/0.98  
% 2.20/0.98  fof(f82,plain,(
% 2.20/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f39])).
% 2.20/0.98  
% 2.20/0.98  fof(f96,plain,(
% 2.20/0.98    v1_tsep_1(sK4,sK2)),
% 2.20/0.98    inference(cnf_transformation,[],[f63])).
% 2.20/0.98  
% 2.20/0.98  fof(f4,axiom,(
% 2.20/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f21,plain,(
% 2.20/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.20/0.98    inference(ennf_transformation,[],[f4])).
% 2.20/0.98  
% 2.20/0.98  fof(f22,plain,(
% 2.20/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.20/0.98    inference(flattening,[],[f21])).
% 2.20/0.98  
% 2.20/0.98  fof(f70,plain,(
% 2.20/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f22])).
% 2.20/0.98  
% 2.20/0.98  fof(f2,axiom,(
% 2.20/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f50,plain,(
% 2.20/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.20/0.98    inference(nnf_transformation,[],[f2])).
% 2.20/0.98  
% 2.20/0.98  fof(f51,plain,(
% 2.20/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.20/0.98    inference(flattening,[],[f50])).
% 2.20/0.98  
% 2.20/0.98  fof(f67,plain,(
% 2.20/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.20/0.98    inference(cnf_transformation,[],[f51])).
% 2.20/0.98  
% 2.20/0.98  fof(f103,plain,(
% 2.20/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.20/0.99    inference(equality_resolution,[],[f67])).
% 2.20/0.99  
% 2.20/0.99  fof(f11,axiom,(
% 2.20/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 2.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/0.99  
% 2.20/0.99  fof(f33,plain,(
% 2.20/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.20/0.99    inference(ennf_transformation,[],[f11])).
% 2.20/0.99  
% 2.20/0.99  fof(f34,plain,(
% 2.20/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/0.99    inference(flattening,[],[f33])).
% 2.20/0.99  
% 2.20/0.99  fof(f77,plain,(
% 2.20/0.99    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.99    inference(cnf_transformation,[],[f34])).
% 2.20/0.99  
% 2.20/0.99  fof(f6,axiom,(
% 2.20/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/0.99  
% 2.20/0.99  fof(f24,plain,(
% 2.20/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.20/0.99    inference(ennf_transformation,[],[f6])).
% 2.20/0.99  
% 2.20/0.99  fof(f25,plain,(
% 2.20/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.20/0.99    inference(flattening,[],[f24])).
% 2.20/0.99  
% 2.20/0.99  fof(f72,plain,(
% 2.20/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/0.99    inference(cnf_transformation,[],[f25])).
% 2.20/0.99  
% 2.20/0.99  fof(f7,axiom,(
% 2.20/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/0.99  
% 2.20/0.99  fof(f26,plain,(
% 2.20/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.20/0.99    inference(ennf_transformation,[],[f7])).
% 2.20/0.99  
% 2.20/0.99  fof(f73,plain,(
% 2.20/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.20/0.99    inference(cnf_transformation,[],[f26])).
% 2.20/0.99  
% 2.20/0.99  fof(f9,axiom,(
% 2.20/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/0.99  
% 2.20/0.99  fof(f29,plain,(
% 2.20/0.99    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.20/0.99    inference(ennf_transformation,[],[f9])).
% 2.20/0.99  
% 2.20/0.99  fof(f30,plain,(
% 2.20/0.99    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/0.99    inference(flattening,[],[f29])).
% 2.20/0.99  
% 2.20/0.99  fof(f75,plain,(
% 2.20/0.99    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.99    inference(cnf_transformation,[],[f30])).
% 2.20/0.99  
% 2.20/0.99  fof(f101,plain,(
% 2.20/0.99    r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | r1_tmap_1(sK2,sK1,sK3,sK5)),
% 2.20/0.99    inference(cnf_transformation,[],[f63])).
% 2.20/0.99  
% 2.20/0.99  cnf(c_25,negated_conjecture,
% 2.20/0.99      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.20/0.99      inference(cnf_transformation,[],[f99]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_3794,plain,
% 2.20/0.99      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 2.20/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_5,plain,
% 2.20/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.20/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_3799,plain,
% 2.20/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 2.20/0.99      | r2_hidden(X0,X1) = iProver_top
% 2.20/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.20/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_4362,plain,
% 2.20/0.99      ( r2_hidden(sK6,u1_struct_0(sK4)) = iProver_top
% 2.20/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 2.20/0.99      inference(superposition,[status(thm)],[c_3794,c_3799]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_7,plain,
% 2.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.20/0.99      | ~ r2_hidden(X2,X0)
% 2.20/0.99      | ~ v1_xboole_0(X1) ),
% 2.20/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_4159,plain,
% 2.20/0.99      ( ~ m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(X0))
% 2.20/0.99      | ~ r2_hidden(sK6,k1_connsp_2(sK4,sK6))
% 2.20/0.99      | ~ v1_xboole_0(X0) ),
% 2.20/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_4338,plain,
% 2.20/0.99      ( ~ m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.20/0.99      | ~ r2_hidden(sK6,k1_connsp_2(sK4,sK6))
% 2.20/0.99      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 2.20/0.99      inference(instantiation,[status(thm)],[c_4159]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_4339,plain,
% 2.20/0.99      ( m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.20/0.99      | r2_hidden(sK6,k1_connsp_2(sK4,sK6)) != iProver_top
% 2.20/0.99      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 2.20/0.99      inference(predicate_to_equality,[status(thm)],[c_4338]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_22,negated_conjecture,
% 2.20/0.99      ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
% 2.20/0.99      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 2.20/0.99      inference(cnf_transformation,[],[f102]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_3796,plain,
% 2.20/0.99      ( r1_tmap_1(sK2,sK1,sK3,sK5) != iProver_top
% 2.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
% 2.20/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_24,negated_conjecture,
% 2.20/0.99      ( sK5 = sK6 ),
% 2.20/0.99      inference(cnf_transformation,[],[f100]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_3882,plain,
% 2.20/0.99      ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
% 2.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
% 2.20/0.99      inference(light_normalisation,[status(thm)],[c_3796,c_24]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_52,plain,
% 2.20/0.99      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 2.20/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_27,negated_conjecture,
% 2.20/0.99      ( m1_pre_topc(sK4,sK2) ),
% 2.20/0.99      inference(cnf_transformation,[],[f97]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_21,plain,
% 2.20/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.20/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.20/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.20/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.20/0.99      | ~ m1_pre_topc(X4,X0)
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.20/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.20/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.20/0.99      | ~ v1_funct_1(X2)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(X4)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ l1_pre_topc(X0)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X0) ),
% 2.20/0.99      inference(cnf_transformation,[],[f110]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_19,plain,
% 2.20/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.20/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.20/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.20/0.99      | ~ m1_pre_topc(X4,X0)
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.20/0.99      | ~ v1_funct_1(X2)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(X4)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ l1_pre_topc(X0)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X0) ),
% 2.20/0.99      inference(cnf_transformation,[],[f108]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_204,plain,
% 2.20/0.99      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.20/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.20/0.99      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.20/0.99      | ~ m1_pre_topc(X4,X0)
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.20/0.99      | ~ v1_funct_1(X2)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(X4)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ l1_pre_topc(X0)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X0) ),
% 2.20/0.99      inference(global_propositional_subsumption,
% 2.20/0.99                [status(thm)],
% 2.20/0.99                [c_21,c_19]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_205,plain,
% 2.20/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.20/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.20/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.20/0.99      | ~ m1_pre_topc(X4,X0)
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.20/0.99      | ~ v1_funct_1(X2)
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | v2_struct_0(X4)
% 2.20/0.99      | ~ l1_pre_topc(X0)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X0)
% 2.20/0.99      | ~ v2_pre_topc(X1) ),
% 2.20/0.99      inference(renaming,[status(thm)],[c_204]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_31,negated_conjecture,
% 2.20/0.99      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 2.20/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_655,plain,
% 2.20/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.20/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.20/0.99      | ~ m1_pre_topc(X4,X0)
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.20/0.99      | ~ v1_funct_1(X2)
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | v2_struct_0(X4)
% 2.20/0.99      | ~ l1_pre_topc(X0)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X0)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.20/0.99      | sK3 != X2 ),
% 2.20/0.99      inference(resolution_lifted,[status(thm)],[c_205,c_31]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_656,plain,
% 2.20/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.20/0.99      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.20/0.99      | ~ m1_pre_topc(X0,X2)
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.20/0.99      | ~ v1_funct_1(sK3)
% 2.20/0.99      | v2_struct_0(X2)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | ~ l1_pre_topc(X2)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X2)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.20/0.99      inference(unflattening,[status(thm)],[c_655]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_32,negated_conjecture,
% 2.20/0.99      ( v1_funct_1(sK3) ),
% 2.20/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_660,plain,
% 2.20/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_pre_topc(X0,X2)
% 2.20/0.99      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.20/0.99      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.20/0.99      | v2_struct_0(X2)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | ~ l1_pre_topc(X2)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X2)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.20/0.99      inference(global_propositional_subsumption,
% 2.20/0.99                [status(thm)],
% 2.20/0.99                [c_656,c_32]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_661,plain,
% 2.20/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.20/0.99      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.20/0.99      | ~ m1_pre_topc(X0,X2)
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(X2)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ l1_pre_topc(X2)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X2)
% 2.20/0.99      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.20/0.99      inference(renaming,[status(thm)],[c_660]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_10,plain,
% 2.20/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.20/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.20/0.99      | m1_subset_1(X2,u1_struct_0(X1))
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | ~ l1_pre_topc(X1) ),
% 2.20/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_696,plain,
% 2.20/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.20/0.99      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.20/0.99      | ~ m1_pre_topc(X0,X2)
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(X2)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ l1_pre_topc(X2)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X2)
% 2.20/0.99      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.20/0.99      inference(forward_subsumption_resolution,
% 2.20/0.99                [status(thm)],
% 2.20/0.99                [c_661,c_10]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_865,plain,
% 2.20/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.20/0.99      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | v2_struct_0(X2)
% 2.20/0.99      | ~ l1_pre_topc(X2)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X2)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.20/0.99      | sK2 != X2
% 2.20/0.99      | sK4 != X0 ),
% 2.20/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_696]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_866,plain,
% 2.20/0.99      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 2.20/0.99      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.20/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(sK2)
% 2.20/0.99      | v2_struct_0(sK4)
% 2.20/0.99      | ~ l1_pre_topc(X0)
% 2.20/0.99      | ~ l1_pre_topc(sK2)
% 2.20/0.99      | ~ v2_pre_topc(X0)
% 2.20/0.99      | ~ v2_pre_topc(sK2)
% 2.20/0.99      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.20/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.20/0.99      inference(unflattening,[status(thm)],[c_865]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_35,negated_conjecture,
% 2.20/0.99      ( ~ v2_struct_0(sK2) ),
% 2.20/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_34,negated_conjecture,
% 2.20/0.99      ( v2_pre_topc(sK2) ),
% 2.20/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_33,negated_conjecture,
% 2.20/0.99      ( l1_pre_topc(sK2) ),
% 2.20/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_29,negated_conjecture,
% 2.20/0.99      ( ~ v2_struct_0(sK4) ),
% 2.20/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_870,plain,
% 2.20/0.99      ( ~ v2_pre_topc(X0)
% 2.20/0.99      | ~ r1_tmap_1(sK2,X0,sK3,X1)
% 2.20/0.99      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.20/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | ~ l1_pre_topc(X0)
% 2.20/0.99      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.20/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.20/0.99      inference(global_propositional_subsumption,
% 2.20/0.99                [status(thm)],
% 2.20/0.99                [c_866,c_35,c_34,c_33,c_29]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_871,plain,
% 2.20/0.99      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 2.20/0.99      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.20/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | ~ l1_pre_topc(X0)
% 2.20/0.99      | ~ v2_pre_topc(X0)
% 2.20/0.99      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.20/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.20/0.99      inference(renaming,[status(thm)],[c_870]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_37,negated_conjecture,
% 2.20/0.99      ( v2_pre_topc(sK1) ),
% 2.20/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_1327,plain,
% 2.20/0.99      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 2.20/0.99      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.20/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | ~ l1_pre_topc(X0)
% 2.20/0.99      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.20/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.20/0.99      | sK1 != X0 ),
% 2.20/0.99      inference(resolution_lifted,[status(thm)],[c_871,c_37]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_1328,plain,
% 2.20/0.99      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 2.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.20/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.20/0.99      | v2_struct_0(sK1)
% 2.20/0.99      | ~ l1_pre_topc(sK1)
% 2.20/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.20/0.99      inference(unflattening,[status(thm)],[c_1327]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_38,negated_conjecture,
% 2.20/0.99      ( ~ v2_struct_0(sK1) ),
% 2.20/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_36,negated_conjecture,
% 2.20/0.99      ( l1_pre_topc(sK1) ),
% 2.20/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_30,negated_conjecture,
% 2.20/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 2.20/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_1332,plain,
% 2.20/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.20/0.99      | ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 2.20/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.20/0.99      inference(global_propositional_subsumption,
% 2.20/0.99                [status(thm)],
% 2.20/0.99                [c_1328,c_38,c_36,c_30]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_1333,plain,
% 2.20/0.99      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 2.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.20/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.20/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.20/0.99      inference(renaming,[status(thm)],[c_1332]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_2231,plain,
% 2.20/0.99      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 2.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.20/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 2.20/0.99      inference(equality_resolution_simp,[status(thm)],[c_1333]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_4046,plain,
% 2.20/0.99      ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
% 2.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 2.20/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.20/0.99      inference(instantiation,[status(thm)],[c_2231]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_4047,plain,
% 2.20/0.99      ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
% 2.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top
% 2.20/0.99      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 2.20/0.99      inference(predicate_to_equality,[status(thm)],[c_4046]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_4055,plain,
% 2.20/0.99      ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top ),
% 2.20/0.99      inference(global_propositional_subsumption,
% 2.20/0.99                [status(thm)],
% 2.20/0.99                [c_3882,c_52,c_4047]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_20,plain,
% 2.20/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.20/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.20/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.20/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.20/0.99      | ~ m1_pre_topc(X4,X0)
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.20/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.20/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.20/0.99      | ~ v1_funct_1(X2)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(X4)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ l1_pre_topc(X0)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X0) ),
% 2.20/0.99      inference(cnf_transformation,[],[f109]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_14,plain,
% 2.20/0.99      ( m1_connsp_2(X0,X1,X2)
% 2.20/0.99      | ~ v3_pre_topc(X0,X1)
% 2.20/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.20/0.99      | ~ r2_hidden(X2,X0)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X1) ),
% 2.20/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_17,plain,
% 2.20/0.99      ( ~ v1_tsep_1(X0,X1)
% 2.20/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.20/0.99      | ~ m1_pre_topc(X0,X1)
% 2.20/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X1) ),
% 2.20/0.99      inference(cnf_transformation,[],[f107]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_18,plain,
% 2.20/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.20/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.20/0.99      | ~ l1_pre_topc(X1) ),
% 2.20/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_212,plain,
% 2.20/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.20/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.20/0.99      | ~ v1_tsep_1(X0,X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X1) ),
% 2.20/0.99      inference(global_propositional_subsumption,
% 2.20/0.99                [status(thm)],
% 2.20/0.99                [c_17,c_18]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_213,plain,
% 2.20/0.99      ( ~ v1_tsep_1(X0,X1)
% 2.20/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.20/0.99      | ~ m1_pre_topc(X0,X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X1) ),
% 2.20/0.99      inference(renaming,[status(thm)],[c_212]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_28,negated_conjecture,
% 2.20/0.99      ( v1_tsep_1(sK4,sK2) ),
% 2.20/0.99      inference(cnf_transformation,[],[f96]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_554,plain,
% 2.20/0.99      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.20/0.99      | ~ m1_pre_topc(X0,X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | sK2 != X1
% 2.20/0.99      | sK4 != X0 ),
% 2.20/0.99      inference(resolution_lifted,[status(thm)],[c_213,c_28]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_555,plain,
% 2.20/0.99      ( v3_pre_topc(u1_struct_0(sK4),sK2)
% 2.20/0.99      | ~ m1_pre_topc(sK4,sK2)
% 2.20/0.99      | ~ l1_pre_topc(sK2)
% 2.20/0.99      | ~ v2_pre_topc(sK2) ),
% 2.20/0.99      inference(unflattening,[status(thm)],[c_554]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_557,plain,
% 2.20/0.99      ( v3_pre_topc(u1_struct_0(sK4),sK2) ),
% 2.20/0.99      inference(global_propositional_subsumption,
% 2.20/0.99                [status(thm)],
% 2.20/0.99                [c_555,c_34,c_33,c_27]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_567,plain,
% 2.20/0.99      ( m1_connsp_2(X0,X1,X2)
% 2.20/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.20/0.99      | ~ r2_hidden(X2,X0)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | u1_struct_0(sK4) != X0
% 2.20/0.99      | sK2 != X1 ),
% 2.20/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_557]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_568,plain,
% 2.20/0.99      ( m1_connsp_2(u1_struct_0(sK4),sK2,X0)
% 2.20/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.20/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.20/0.99      | ~ r2_hidden(X0,u1_struct_0(sK4))
% 2.20/0.99      | v2_struct_0(sK2)
% 2.20/0.99      | ~ l1_pre_topc(sK2)
% 2.20/0.99      | ~ v2_pre_topc(sK2) ),
% 2.20/0.99      inference(unflattening,[status(thm)],[c_567]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_572,plain,
% 2.20/0.99      ( ~ r2_hidden(X0,u1_struct_0(sK4))
% 2.20/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.20/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.20/0.99      | m1_connsp_2(u1_struct_0(sK4),sK2,X0) ),
% 2.20/0.99      inference(global_propositional_subsumption,
% 2.20/0.99                [status(thm)],
% 2.20/0.99                [c_568,c_35,c_34,c_33]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_573,plain,
% 2.20/0.99      ( m1_connsp_2(u1_struct_0(sK4),sK2,X0)
% 2.20/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.20/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.20/0.99      | ~ r2_hidden(X0,u1_struct_0(sK4)) ),
% 2.20/0.99      inference(renaming,[status(thm)],[c_572]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_6,plain,
% 2.20/0.99      ( m1_subset_1(X0,X1)
% 2.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.20/0.99      | ~ r2_hidden(X0,X2) ),
% 2.20/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_586,plain,
% 2.20/0.99      ( m1_connsp_2(u1_struct_0(sK4),sK2,X0)
% 2.20/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.20/0.99      | ~ r2_hidden(X0,u1_struct_0(sK4)) ),
% 2.20/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_573,c_6]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_599,plain,
% 2.20/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.20/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.20/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.20/0.99      | ~ m1_pre_topc(X4,X0)
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.20/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.20/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.20/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.20/0.99      | ~ r2_hidden(X6,u1_struct_0(sK4))
% 2.20/0.99      | ~ v1_funct_1(X2)
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | v2_struct_0(X4)
% 2.20/0.99      | ~ l1_pre_topc(X0)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X0)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | X6 != X3
% 2.20/0.99      | u1_struct_0(sK4) != X5
% 2.20/0.99      | sK2 != X0 ),
% 2.20/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_586]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_600,plain,
% 2.20/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,X2,X0),X3)
% 2.20/0.99      | r1_tmap_1(sK2,X1,X2,X3)
% 2.20/0.99      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
% 2.20/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 2.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 2.20/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.20/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 2.20/0.99      | ~ r2_hidden(X3,u1_struct_0(sK4))
% 2.20/0.99      | ~ v1_funct_1(X2)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(sK2)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ l1_pre_topc(sK2)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(sK2) ),
% 2.20/0.99      inference(unflattening,[status(thm)],[c_599]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_604,plain,
% 2.20/0.99      ( ~ v2_pre_topc(X1)
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | ~ v1_funct_1(X2)
% 2.20/0.99      | ~ r2_hidden(X3,u1_struct_0(sK4))
% 2.20/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.20/0.99      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
% 2.20/0.99      | r1_tmap_1(sK2,X1,X2,X3)
% 2.20/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,X2,X0),X3)
% 2.20/0.99      | ~ l1_pre_topc(X1) ),
% 2.20/0.99      inference(global_propositional_subsumption,
% 2.20/0.99                [status(thm)],
% 2.20/0.99                [c_600,c_35,c_34,c_33]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_605,plain,
% 2.20/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,X2,X0),X3)
% 2.20/0.99      | r1_tmap_1(sK2,X1,X2,X3)
% 2.20/0.99      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
% 2.20/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 2.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 2.20/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.20/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 2.20/0.99      | ~ r2_hidden(X3,u1_struct_0(sK4))
% 2.20/0.99      | ~ v1_funct_1(X2)
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X1) ),
% 2.20/0.99      inference(renaming,[status(thm)],[c_604]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_638,plain,
% 2.20/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,X2,X0),X3)
% 2.20/0.99      | r1_tmap_1(sK2,X1,X2,X3)
% 2.20/0.99      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
% 2.20/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 2.20/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.20/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 2.20/0.99      | ~ r2_hidden(X3,u1_struct_0(sK4))
% 2.20/0.99      | ~ v1_funct_1(X2)
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X1) ),
% 2.20/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_605,c_6]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_761,plain,
% 2.20/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,X2,X0),X3)
% 2.20/0.99      | r1_tmap_1(sK2,X1,X2,X3)
% 2.20/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 2.20/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.20/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 2.20/0.99      | ~ r2_hidden(X3,u1_struct_0(sK4))
% 2.20/0.99      | ~ v1_funct_1(X2)
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.20/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.20/0.99      | sK3 != X2 ),
% 2.20/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_638]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_762,plain,
% 2.20/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
% 2.20/0.99      | r1_tmap_1(sK2,X1,sK3,X2)
% 2.20/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.20/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 2.20/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 2.20/0.99      | ~ r2_hidden(X2,u1_struct_0(sK4))
% 2.20/0.99      | ~ v1_funct_1(sK3)
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.20/0.99      inference(unflattening,[status(thm)],[c_761]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_766,plain,
% 2.20/0.99      ( ~ r2_hidden(X2,u1_struct_0(sK4))
% 2.20/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 2.20/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.20/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.20/0.99      | r1_tmap_1(sK2,X1,sK3,X2)
% 2.20/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.20/0.99      inference(global_propositional_subsumption,
% 2.20/0.99                [status(thm)],
% 2.20/0.99                [c_762,c_32]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_767,plain,
% 2.20/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
% 2.20/0.99      | r1_tmap_1(sK2,X1,sK3,X2)
% 2.20/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.20/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 2.20/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 2.20/0.99      | ~ r2_hidden(X2,u1_struct_0(sK4))
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.20/0.99      inference(renaming,[status(thm)],[c_766]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_904,plain,
% 2.20/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
% 2.20/0.99      | r1_tmap_1(sK2,X1,sK3,X2)
% 2.20/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.20/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 2.20/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 2.20/0.99      | ~ r2_hidden(X2,u1_struct_0(sK4))
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.20/0.99      | sK2 != sK2
% 2.20/0.99      | sK4 != X0 ),
% 2.20/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_767]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_905,plain,
% 2.20/0.99      ( r1_tmap_1(sK2,X0,sK3,X1)
% 2.20/0.99      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.20/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.20/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.20/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
% 2.20/0.99      | ~ r2_hidden(X1,u1_struct_0(sK4))
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | v2_struct_0(sK4)
% 2.20/0.99      | ~ l1_pre_topc(X0)
% 2.20/0.99      | ~ v2_pre_topc(X0)
% 2.20/0.99      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 2.20/0.99      inference(unflattening,[status(thm)],[c_904]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_814,plain,
% 2.20/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | sK2 != X1
% 2.20/0.99      | sK4 != X0 ),
% 2.20/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_815,plain,
% 2.20/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.20/0.99      | ~ l1_pre_topc(sK2) ),
% 2.20/0.99      inference(unflattening,[status(thm)],[c_814]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_909,plain,
% 2.20/0.99      ( v2_struct_0(X0)
% 2.20/0.99      | ~ r2_hidden(X1,u1_struct_0(sK4))
% 2.20/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.20/0.99      | r1_tmap_1(sK2,X0,sK3,X1)
% 2.20/0.99      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.20/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.20/0.99      | ~ l1_pre_topc(X0)
% 2.20/0.99      | ~ v2_pre_topc(X0)
% 2.20/0.99      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 2.20/0.99      inference(global_propositional_subsumption,
% 2.20/0.99                [status(thm)],
% 2.20/0.99                [c_905,c_33,c_29,c_815]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_910,plain,
% 2.20/0.99      ( r1_tmap_1(sK2,X0,sK3,X1)
% 2.20/0.99      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.20/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.20/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
% 2.20/0.99      | ~ r2_hidden(X1,u1_struct_0(sK4))
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | ~ l1_pre_topc(X0)
% 2.20/0.99      | ~ v2_pre_topc(X0)
% 2.20/0.99      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 2.20/0.99      inference(renaming,[status(thm)],[c_909]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_3,plain,
% 2.20/0.99      ( r1_tarski(X0,X0) ),
% 2.20/0.99      inference(cnf_transformation,[],[f103]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_935,plain,
% 2.20/0.99      ( r1_tmap_1(sK2,X0,sK3,X1)
% 2.20/0.99      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.20/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.20/0.99      | ~ r2_hidden(X1,u1_struct_0(sK4))
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | ~ l1_pre_topc(X0)
% 2.20/0.99      | ~ v2_pre_topc(X0)
% 2.20/0.99      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 2.20/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_910,c_3]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_1300,plain,
% 2.20/0.99      ( r1_tmap_1(sK2,X0,sK3,X1)
% 2.20/0.99      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.20/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.20/0.99      | ~ r2_hidden(X1,u1_struct_0(sK4))
% 2.20/0.99      | v2_struct_0(X0)
% 2.20/0.99      | ~ l1_pre_topc(X0)
% 2.20/0.99      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.20/0.99      | sK1 != X0 ),
% 2.20/0.99      inference(resolution_lifted,[status(thm)],[c_935,c_37]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_1301,plain,
% 2.20/0.99      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 2.20/0.99      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.20/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.20/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.20/0.99      | ~ r2_hidden(X0,u1_struct_0(sK4))
% 2.20/0.99      | v2_struct_0(sK1)
% 2.20/0.99      | ~ l1_pre_topc(sK1)
% 2.20/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.20/0.99      inference(unflattening,[status(thm)],[c_1300]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_1305,plain,
% 2.20/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.20/0.99      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.20/0.99      | r1_tmap_1(sK2,sK1,sK3,X0)
% 2.20/0.99      | ~ r2_hidden(X0,u1_struct_0(sK4))
% 2.20/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.20/0.99      inference(global_propositional_subsumption,
% 2.20/0.99                [status(thm)],
% 2.20/0.99                [c_1301,c_38,c_36,c_30]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_1306,plain,
% 2.20/0.99      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 2.20/0.99      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.20/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.20/0.99      | ~ r2_hidden(X0,u1_struct_0(sK4))
% 2.20/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.20/0.99      inference(renaming,[status(thm)],[c_1305]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_2235,plain,
% 2.20/0.99      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 2.20/0.99      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.20/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.20/0.99      | ~ r2_hidden(X0,u1_struct_0(sK4)) ),
% 2.20/0.99      inference(equality_resolution_simp,[status(thm)],[c_1306]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_4049,plain,
% 2.20/0.99      ( r1_tmap_1(sK2,sK1,sK3,sK6)
% 2.20/0.99      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 2.20/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.20/0.99      | ~ r2_hidden(sK6,u1_struct_0(sK4)) ),
% 2.20/0.99      inference(instantiation,[status(thm)],[c_2235]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_4050,plain,
% 2.20/0.99      ( r1_tmap_1(sK2,sK1,sK3,sK6) = iProver_top
% 2.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top
% 2.20/0.99      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 2.20/0.99      | r2_hidden(sK6,u1_struct_0(sK4)) != iProver_top ),
% 2.20/0.99      inference(predicate_to_equality,[status(thm)],[c_4049]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_13,plain,
% 2.20/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.20/0.99      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X1) ),
% 2.20/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_8,plain,
% 2.20/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X1)
% 2.20/0.99      | v2_pre_topc(X0) ),
% 2.20/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_854,plain,
% 2.20/0.99      ( ~ l1_pre_topc(X0)
% 2.20/0.99      | ~ v2_pre_topc(X0)
% 2.20/0.99      | v2_pre_topc(X1)
% 2.20/0.99      | sK2 != X0
% 2.20/0.99      | sK4 != X1 ),
% 2.20/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_27]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_855,plain,
% 2.20/0.99      ( ~ l1_pre_topc(sK2) | ~ v2_pre_topc(sK2) | v2_pre_topc(sK4) ),
% 2.20/0.99      inference(unflattening,[status(thm)],[c_854]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_857,plain,
% 2.20/0.99      ( v2_pre_topc(sK4) ),
% 2.20/0.99      inference(global_propositional_subsumption,
% 2.20/0.99                [status(thm)],
% 2.20/0.99                [c_855,c_34,c_33]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_1480,plain,
% 2.20/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.20/0.99      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | sK4 != X1 ),
% 2.20/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_857]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_1481,plain,
% 2.20/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.20/0.99      | r2_hidden(X0,k1_connsp_2(sK4,X0))
% 2.20/0.99      | v2_struct_0(sK4)
% 2.20/0.99      | ~ l1_pre_topc(sK4) ),
% 2.20/0.99      inference(unflattening,[status(thm)],[c_1480]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_9,plain,
% 2.20/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.20/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_843,plain,
% 2.20/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X0 | sK4 != X1 ),
% 2.20/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_27]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_844,plain,
% 2.20/0.99      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK4) ),
% 2.20/0.99      inference(unflattening,[status(thm)],[c_843]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_1485,plain,
% 2.20/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.20/0.99      | r2_hidden(X0,k1_connsp_2(sK4,X0)) ),
% 2.20/0.99      inference(global_propositional_subsumption,
% 2.20/0.99                [status(thm)],
% 2.20/0.99                [c_1481,c_33,c_29,c_844]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_4039,plain,
% 2.20/0.99      ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.20/0.99      | r2_hidden(sK6,k1_connsp_2(sK4,sK6)) ),
% 2.20/0.99      inference(instantiation,[status(thm)],[c_1485]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_4040,plain,
% 2.20/0.99      ( m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 2.20/0.99      | r2_hidden(sK6,k1_connsp_2(sK4,sK6)) = iProver_top ),
% 2.20/0.99      inference(predicate_to_equality,[status(thm)],[c_4039]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_11,plain,
% 2.20/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.20/0.99      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | ~ v2_pre_topc(X1) ),
% 2.20/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_1498,plain,
% 2.20/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.20/0.99      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.20/0.99      | v2_struct_0(X1)
% 2.20/0.99      | ~ l1_pre_topc(X1)
% 2.20/0.99      | sK4 != X1 ),
% 2.20/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_857]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_1499,plain,
% 2.20/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.20/0.99      | m1_subset_1(k1_connsp_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.20/0.99      | v2_struct_0(sK4)
% 2.20/0.99      | ~ l1_pre_topc(sK4) ),
% 2.20/0.99      inference(unflattening,[status(thm)],[c_1498]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_1503,plain,
% 2.20/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.20/0.99      | m1_subset_1(k1_connsp_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.20/0.99      inference(global_propositional_subsumption,
% 2.20/0.99                [status(thm)],
% 2.20/0.99                [c_1499,c_33,c_29,c_844]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_4036,plain,
% 2.20/0.99      ( m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.20/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.20/0.99      inference(instantiation,[status(thm)],[c_1503]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_4037,plain,
% 2.20/0.99      ( m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.20/0.99      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 2.20/0.99      inference(predicate_to_equality,[status(thm)],[c_4036]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_23,negated_conjecture,
% 2.20/0.99      ( r1_tmap_1(sK2,sK1,sK3,sK5)
% 2.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 2.20/0.99      inference(cnf_transformation,[],[f101]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_3795,plain,
% 2.20/0.99      ( r1_tmap_1(sK2,sK1,sK3,sK5) = iProver_top
% 2.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
% 2.20/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(c_3865,plain,
% 2.20/0.99      ( r1_tmap_1(sK2,sK1,sK3,sK6) = iProver_top
% 2.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
% 2.20/0.99      inference(light_normalisation,[status(thm)],[c_3795,c_24]) ).
% 2.20/0.99  
% 2.20/0.99  cnf(contradiction,plain,
% 2.20/0.99      ( $false ),
% 2.20/0.99      inference(minisat,
% 2.20/0.99                [status(thm)],
% 2.20/0.99                [c_4362,c_4339,c_4055,c_4050,c_4040,c_4037,c_3865,c_52]) ).
% 2.20/0.99  
% 2.20/0.99  
% 2.20/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.20/0.99  
% 2.20/0.99  ------                               Statistics
% 2.20/0.99  
% 2.20/0.99  ------ General
% 2.20/0.99  
% 2.20/0.99  abstr_ref_over_cycles:                  0
% 2.20/0.99  abstr_ref_under_cycles:                 0
% 2.20/0.99  gc_basic_clause_elim:                   0
% 2.20/0.99  forced_gc_time:                         0
% 2.20/0.99  parsing_time:                           0.007
% 2.20/0.99  unif_index_cands_time:                  0.
% 2.20/0.99  unif_index_add_time:                    0.
% 2.20/0.99  orderings_time:                         0.
% 2.20/0.99  out_proof_time:                         0.015
% 2.20/0.99  total_time:                             0.179
% 2.20/0.99  num_of_symbols:                         61
% 2.20/0.99  num_of_terms:                           1883
% 2.20/0.99  
% 2.20/0.99  ------ Preprocessing
% 2.20/0.99  
% 2.20/0.99  num_of_splits:                          4
% 2.20/0.99  num_of_split_atoms:                     4
% 2.20/0.99  num_of_reused_defs:                     0
% 2.20/0.99  num_eq_ax_congr_red:                    19
% 2.20/0.99  num_of_sem_filtered_clauses:            1
% 2.20/0.99  num_of_subtypes:                        0
% 2.20/0.99  monotx_restored_types:                  0
% 2.20/0.99  sat_num_of_epr_types:                   0
% 2.20/0.99  sat_num_of_non_cyclic_types:            0
% 2.20/0.99  sat_guarded_non_collapsed_types:        0
% 2.20/0.99  num_pure_diseq_elim:                    0
% 2.20/0.99  simp_replaced_by:                       0
% 2.20/0.99  res_preprocessed:                       147
% 2.20/0.99  prep_upred:                             0
% 2.20/0.99  prep_unflattend:                        159
% 2.20/0.99  smt_new_axioms:                         0
% 2.20/0.99  pred_elim_cands:                        5
% 2.20/0.99  pred_elim:                              9
% 2.20/0.99  pred_elim_cl:                           10
% 2.20/0.99  pred_elim_cycles:                       14
% 2.20/0.99  merged_defs:                            8
% 2.20/0.99  merged_defs_ncl:                        0
% 2.20/0.99  bin_hyper_res:                          8
% 2.20/0.99  prep_cycles:                            4
% 2.20/0.99  pred_elim_time:                         0.078
% 2.20/0.99  splitting_time:                         0.
% 2.20/0.99  sem_filter_time:                        0.
% 2.20/0.99  monotx_time:                            0.001
% 2.20/0.99  subtype_inf_time:                       0.
% 2.20/0.99  
% 2.20/0.99  ------ Problem properties
% 2.20/0.99  
% 2.20/0.99  clauses:                                31
% 2.20/0.99  conjectures:                            6
% 2.20/0.99  epr:                                    5
% 2.20/0.99  horn:                                   28
% 2.20/0.99  ground:                                 11
% 2.20/0.99  unary:                                  6
% 2.20/0.99  binary:                                 11
% 2.20/0.99  lits:                                   77
% 2.20/0.99  lits_eq:                                6
% 2.20/0.99  fd_pure:                                0
% 2.20/0.99  fd_pseudo:                              0
% 2.20/0.99  fd_cond:                                0
% 2.20/0.99  fd_pseudo_cond:                         1
% 2.20/0.99  ac_symbols:                             0
% 2.20/0.99  
% 2.20/0.99  ------ Propositional Solver
% 2.20/0.99  
% 2.20/0.99  prop_solver_calls:                      24
% 2.20/0.99  prop_fast_solver_calls:                 1576
% 2.20/0.99  smt_solver_calls:                       0
% 2.20/0.99  smt_fast_solver_calls:                  0
% 2.20/0.99  prop_num_of_clauses:                    706
% 2.20/0.99  prop_preprocess_simplified:             4558
% 2.20/0.99  prop_fo_subsumed:                       65
% 2.20/0.99  prop_solver_time:                       0.
% 2.20/0.99  smt_solver_time:                        0.
% 2.20/0.99  smt_fast_solver_time:                   0.
% 2.20/0.99  prop_fast_solver_time:                  0.
% 2.20/0.99  prop_unsat_core_time:                   0.
% 2.20/0.99  
% 2.20/0.99  ------ QBF
% 2.20/0.99  
% 2.20/0.99  qbf_q_res:                              0
% 2.20/0.99  qbf_num_tautologies:                    0
% 2.20/0.99  qbf_prep_cycles:                        0
% 2.20/0.99  
% 2.20/0.99  ------ BMC1
% 2.20/0.99  
% 2.20/0.99  bmc1_current_bound:                     -1
% 2.20/0.99  bmc1_last_solved_bound:                 -1
% 2.20/0.99  bmc1_unsat_core_size:                   -1
% 2.20/0.99  bmc1_unsat_core_parents_size:           -1
% 2.20/0.99  bmc1_merge_next_fun:                    0
% 2.20/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.20/0.99  
% 2.20/0.99  ------ Instantiation
% 2.20/0.99  
% 2.20/0.99  inst_num_of_clauses:                    116
% 2.20/0.99  inst_num_in_passive:                    16
% 2.20/0.99  inst_num_in_active:                     69
% 2.20/0.99  inst_num_in_unprocessed:                31
% 2.20/0.99  inst_num_of_loops:                      70
% 2.20/0.99  inst_num_of_learning_restarts:          0
% 2.20/0.99  inst_num_moves_active_passive:          0
% 2.20/0.99  inst_lit_activity:                      0
% 2.20/0.99  inst_lit_activity_moves:                0
% 2.20/0.99  inst_num_tautologies:                   0
% 2.20/0.99  inst_num_prop_implied:                  0
% 2.20/0.99  inst_num_existing_simplified:           0
% 2.20/0.99  inst_num_eq_res_simplified:             0
% 2.20/0.99  inst_num_child_elim:                    0
% 2.20/0.99  inst_num_of_dismatching_blockings:      0
% 2.20/0.99  inst_num_of_non_proper_insts:           63
% 2.20/0.99  inst_num_of_duplicates:                 0
% 2.20/0.99  inst_inst_num_from_inst_to_res:         0
% 2.20/0.99  inst_dismatching_checking_time:         0.
% 2.20/0.99  
% 2.20/0.99  ------ Resolution
% 2.20/0.99  
% 2.20/0.99  res_num_of_clauses:                     0
% 2.20/0.99  res_num_in_passive:                     0
% 2.20/0.99  res_num_in_active:                      0
% 2.20/0.99  res_num_of_loops:                       151
% 2.20/0.99  res_forward_subset_subsumed:            4
% 2.20/0.99  res_backward_subset_subsumed:           0
% 2.20/0.99  res_forward_subsumed:                   3
% 2.20/0.99  res_backward_subsumed:                  7
% 2.20/0.99  res_forward_subsumption_resolution:     4
% 2.20/0.99  res_backward_subsumption_resolution:    0
% 2.20/0.99  res_clause_to_clause_subsumption:       149
% 2.20/0.99  res_orphan_elimination:                 0
% 2.20/0.99  res_tautology_del:                      25
% 2.20/0.99  res_num_eq_res_simplified:              2
% 2.20/0.99  res_num_sel_changes:                    0
% 2.20/0.99  res_moves_from_active_to_pass:          0
% 2.20/0.99  
% 2.20/0.99  ------ Superposition
% 2.20/0.99  
% 2.20/0.99  sup_time_total:                         0.
% 2.20/0.99  sup_time_generating:                    0.
% 2.20/0.99  sup_time_sim_full:                      0.
% 2.20/0.99  sup_time_sim_immed:                     0.
% 2.20/0.99  
% 2.20/0.99  sup_num_of_clauses:                     34
% 2.20/0.99  sup_num_in_active:                      13
% 2.20/0.99  sup_num_in_passive:                     21
% 2.20/0.99  sup_num_of_loops:                       12
% 2.20/0.99  sup_fw_superposition:                   7
% 2.20/0.99  sup_bw_superposition:                   0
% 2.20/0.99  sup_immediate_simplified:               0
% 2.20/0.99  sup_given_eliminated:                   0
% 2.20/0.99  comparisons_done:                       0
% 2.20/0.99  comparisons_avoided:                    0
% 2.20/0.99  
% 2.20/0.99  ------ Simplifications
% 2.20/0.99  
% 2.20/0.99  
% 2.20/0.99  sim_fw_subset_subsumed:                 0
% 2.20/0.99  sim_bw_subset_subsumed:                 0
% 2.20/0.99  sim_fw_subsumed:                        0
% 2.20/0.99  sim_bw_subsumed:                        0
% 2.20/0.99  sim_fw_subsumption_res:                 0
% 2.20/0.99  sim_bw_subsumption_res:                 0
% 2.20/0.99  sim_tautology_del:                      0
% 2.20/0.99  sim_eq_tautology_del:                   0
% 2.20/0.99  sim_eq_res_simp:                        0
% 2.20/0.99  sim_fw_demodulated:                     0
% 2.20/0.99  sim_bw_demodulated:                     0
% 2.20/0.99  sim_light_normalised:                   3
% 2.20/0.99  sim_joinable_taut:                      0
% 2.20/0.99  sim_joinable_simp:                      0
% 2.20/0.99  sim_ac_normalised:                      0
% 2.20/0.99  sim_smt_subsumption:                    0
% 2.20/0.99  
%------------------------------------------------------------------------------
