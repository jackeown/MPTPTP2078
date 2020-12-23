%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:41 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 944 expanded)
%              Number of clauses        :  111 ( 156 expanded)
%              Number of leaves         :   21 ( 372 expanded)
%              Depth                    :   33
%              Number of atoms          : 1453 (14837 expanded)
%              Number of equality atoms :  122 (1063 expanded)
%              Maximal formula depth    :   28 (   8 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(negated_conjecture,[],[f14])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(nnf_transformation,[],[f38])).

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
     => ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6)
          | ~ r1_tmap_1(X1,X0,X2,X4) )
        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6)
          | r1_tmap_1(X1,X0,X2,X4) )
        & sK6 = X4
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
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
              | ~ r1_tmap_1(X1,X0,X2,sK5) )
            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
              | r1_tmap_1(X1,X0,X2,sK5) )
            & sK5 = X5
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_subset_1(sK5,u1_struct_0(X1)) ) ) ),
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

fof(f54,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f47,f53,f52,f51,f50,f49,f48])).

fof(f89,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | ~ r1_tmap_1(sK2,sK1,sK3,sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(nnf_transformation,[],[f36])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f97,plain,(
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
    inference(equality_resolution,[],[f71])).

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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(cnf_transformation,[],[f34])).

fof(f95,plain,(
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
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
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

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f22])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f77,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f78,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f74,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f73,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f75,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f96,plain,(
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
    inference(equality_resolution,[],[f72])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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

fof(f94,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

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

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

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

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK0(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f41])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f88,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | r1_tmap_1(sK2,sK1,sK3,sK5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3439,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3676,plain,
    ( ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,sK0(sK4,sK6))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3439])).

cnf(c_3840,plain,
    ( ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK6,sK0(sK4,sK6))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3676])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3098,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK5) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3167,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3098,c_20])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_48,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_17,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X5,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X5)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f95])).

cnf(c_180,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
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
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_180])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_582,plain,
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
    inference(resolution_lifted,[status(thm)],[c_181,c_27])).

cnf(c_583,plain,
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
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_587,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_583,c_28])).

cnf(c_588,plain,
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
    inference(renaming,[status(thm)],[c_587])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_623,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_588,c_7])).

cnf(c_795,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_623])).

cnf(c_796,plain,
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
    inference(unflattening,[status(thm)],[c_795])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_800,plain,
    ( ~ v2_pre_topc(X0)
    | ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_796,c_31,c_30,c_29,c_25])).

cnf(c_801,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_800])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1130,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_801,c_33])).

cnf(c_1131,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1130])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1135,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1131,c_34,c_32,c_26])).

cnf(c_1136,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1135])).

cnf(c_1837,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1136])).

cnf(c_3325,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1837])).

cnf(c_3326,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3325])).

cnf(c_3346,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3167,c_48,c_3326])).

cnf(c_3348,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3346])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3331,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | r2_hidden(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_16,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X5,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X5)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_13,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_188,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_14])).

cnf(c_189,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_188])).

cnf(c_24,negated_conjecture,
    ( v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_459,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_189,c_24])).

cnf(c_460,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_462,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_30,c_29,c_23])).

cnf(c_526,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X5)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(sK4) != X5
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_462])).

cnf(c_527,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,X2,X0),X3)
    | r1_tmap_1(sK2,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X3,u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_531,plain,
    ( ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X2)
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | ~ r2_hidden(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK2)
    | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
    | r1_tmap_1(sK2,X1,X2,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,X2,X0),X3)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_527,c_31,c_30,c_29])).

cnf(c_532,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,X2,X0),X3)
    | r1_tmap_1(sK2,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X3,u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_531])).

cnf(c_688,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,X2,X0),X3)
    | r1_tmap_1(sK2,X1,X2,X3)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X3,u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_532])).

cnf(c_689,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
    | r1_tmap_1(sK2,X1,sK3,X2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ r2_hidden(X2,u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | ~ v1_funct_1(sK3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_693,plain,
    ( ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | ~ r2_hidden(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK2)
    | r1_tmap_1(sK2,X1,sK3,X2)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_689,c_28])).

cnf(c_694,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
    | r1_tmap_1(sK2,X1,sK3,X2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ r2_hidden(X2,u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_693])).

cnf(c_834,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
    | r1_tmap_1(sK2,X1,sK3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ r2_hidden(X2,u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != sK2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_694])).

cnf(c_835,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r2_hidden(X1,u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_834])).

cnf(c_744,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_745,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_744])).

cnf(c_839,plain,
    ( v2_struct_0(X0)
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ r2_hidden(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_835,c_29,c_25,c_745])).

cnf(c_840,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r2_hidden(X1,u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_839])).

cnf(c_755,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | sK2 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_756,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_755])).

cnf(c_760,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_756,c_31,c_29,c_25])).

cnf(c_761,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_760])).

cnf(c_856,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r2_hidden(X1,u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_840,c_761])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_867,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r2_hidden(X1,u1_struct_0(sK4))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_856,c_1])).

cnf(c_1103,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r2_hidden(X1,u1_struct_0(sK4))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_867,c_33])).

cnf(c_1104,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ r2_hidden(X0,u1_struct_0(sK4))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1103])).

cnf(c_1108,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r2_hidden(X0,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1104,c_34,c_32,c_26])).

cnf(c_1109,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1108])).

cnf(c_1841,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,u1_struct_0(sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1109])).

cnf(c_3328,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1841])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_8,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_202,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_8])).

cnf(c_203,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_202])).

cnf(c_9,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_472,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | r2_hidden(X0,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | X3 != X1
    | X2 != X0
    | sK0(X3,X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_203,c_9])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,sK0(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_784,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_785,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_784])).

cnf(c_787,plain,
    ( v2_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_785,c_30,c_29])).

cnf(c_1301,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,sK0(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_473,c_787])).

cnf(c_1302,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,sK0(sK4,X0))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1301])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_773,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_774,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_773])).

cnf(c_1306,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,sK0(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1302,c_29,c_25,c_774])).

cnf(c_3318,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | r2_hidden(sK6,sK0(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_1306])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | X3 != X1
    | X2 != X0
    | sK0(X3,X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_1283,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_494,c_787])).

cnf(c_1284,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1283])).

cnf(c_1288,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1284,c_29,c_25,c_774])).

cnf(c_3315,plain,
    ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1288])).

cnf(c_19,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,sK3,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3097,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK5) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3156,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3097,c_20])).

cnf(c_3251,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3156])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3840,c_3348,c_3331,c_3328,c_3318,c_3315,c_3251,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : iproveropt_run.sh %d %s
% 0.08/0.29  % Computer   : n017.cluster.edu
% 0.08/0.29  % Model      : x86_64 x86_64
% 0.08/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.29  % Memory     : 8042.1875MB
% 0.08/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.29  % CPULimit   : 60
% 0.08/0.29  % WCLimit    : 600
% 0.08/0.29  % DateTime   : Tue Dec  1 12:54:16 EST 2020
% 0.08/0.29  % CPUTime    : 
% 0.08/0.30  % Running in FOF mode
% 1.68/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/0.96  
% 1.68/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.68/0.96  
% 1.68/0.96  ------  iProver source info
% 1.68/0.96  
% 1.68/0.96  git: date: 2020-06-30 10:37:57 +0100
% 1.68/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.68/0.96  git: non_committed_changes: false
% 1.68/0.96  git: last_make_outside_of_git: false
% 1.68/0.96  
% 1.68/0.96  ------ 
% 1.68/0.96  
% 1.68/0.96  ------ Input Options
% 1.68/0.96  
% 1.68/0.96  --out_options                           all
% 1.68/0.96  --tptp_safe_out                         true
% 1.68/0.96  --problem_path                          ""
% 1.68/0.96  --include_path                          ""
% 1.68/0.96  --clausifier                            res/vclausify_rel
% 1.68/0.96  --clausifier_options                    --mode clausify
% 1.68/0.96  --stdin                                 false
% 1.68/0.96  --stats_out                             all
% 1.68/0.96  
% 1.68/0.96  ------ General Options
% 1.68/0.96  
% 1.68/0.96  --fof                                   false
% 1.68/0.96  --time_out_real                         305.
% 1.68/0.96  --time_out_virtual                      -1.
% 1.68/0.96  --symbol_type_check                     false
% 1.68/0.96  --clausify_out                          false
% 1.68/0.96  --sig_cnt_out                           false
% 1.68/0.96  --trig_cnt_out                          false
% 1.68/0.96  --trig_cnt_out_tolerance                1.
% 1.68/0.96  --trig_cnt_out_sk_spl                   false
% 1.68/0.96  --abstr_cl_out                          false
% 1.68/0.96  
% 1.68/0.96  ------ Global Options
% 1.68/0.96  
% 1.68/0.96  --schedule                              default
% 1.68/0.96  --add_important_lit                     false
% 1.68/0.96  --prop_solver_per_cl                    1000
% 1.68/0.96  --min_unsat_core                        false
% 1.68/0.96  --soft_assumptions                      false
% 1.68/0.96  --soft_lemma_size                       3
% 1.68/0.96  --prop_impl_unit_size                   0
% 1.68/0.96  --prop_impl_unit                        []
% 1.68/0.96  --share_sel_clauses                     true
% 1.68/0.96  --reset_solvers                         false
% 1.68/0.96  --bc_imp_inh                            [conj_cone]
% 1.68/0.96  --conj_cone_tolerance                   3.
% 1.68/0.96  --extra_neg_conj                        none
% 1.68/0.96  --large_theory_mode                     true
% 1.68/0.96  --prolific_symb_bound                   200
% 1.68/0.96  --lt_threshold                          2000
% 1.68/0.96  --clause_weak_htbl                      true
% 1.68/0.96  --gc_record_bc_elim                     false
% 1.68/0.96  
% 1.68/0.96  ------ Preprocessing Options
% 1.68/0.96  
% 1.68/0.96  --preprocessing_flag                    true
% 1.68/0.96  --time_out_prep_mult                    0.1
% 1.68/0.96  --splitting_mode                        input
% 1.68/0.96  --splitting_grd                         true
% 1.68/0.96  --splitting_cvd                         false
% 1.68/0.96  --splitting_cvd_svl                     false
% 1.68/0.96  --splitting_nvd                         32
% 1.68/0.96  --sub_typing                            true
% 1.68/0.96  --prep_gs_sim                           true
% 1.68/0.96  --prep_unflatten                        true
% 1.68/0.96  --prep_res_sim                          true
% 1.68/0.96  --prep_upred                            true
% 1.68/0.96  --prep_sem_filter                       exhaustive
% 1.68/0.96  --prep_sem_filter_out                   false
% 1.68/0.96  --pred_elim                             true
% 1.68/0.96  --res_sim_input                         true
% 1.68/0.96  --eq_ax_congr_red                       true
% 1.68/0.96  --pure_diseq_elim                       true
% 1.68/0.96  --brand_transform                       false
% 1.68/0.96  --non_eq_to_eq                          false
% 1.68/0.96  --prep_def_merge                        true
% 1.68/0.96  --prep_def_merge_prop_impl              false
% 1.68/0.96  --prep_def_merge_mbd                    true
% 1.68/0.96  --prep_def_merge_tr_red                 false
% 1.68/0.96  --prep_def_merge_tr_cl                  false
% 1.68/0.96  --smt_preprocessing                     true
% 1.68/0.96  --smt_ac_axioms                         fast
% 1.68/0.96  --preprocessed_out                      false
% 1.68/0.96  --preprocessed_stats                    false
% 1.68/0.96  
% 1.68/0.96  ------ Abstraction refinement Options
% 1.68/0.96  
% 1.68/0.96  --abstr_ref                             []
% 1.68/0.96  --abstr_ref_prep                        false
% 1.68/0.96  --abstr_ref_until_sat                   false
% 1.68/0.96  --abstr_ref_sig_restrict                funpre
% 1.68/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.68/0.96  --abstr_ref_under                       []
% 1.68/0.96  
% 1.68/0.96  ------ SAT Options
% 1.68/0.96  
% 1.68/0.96  --sat_mode                              false
% 1.68/0.96  --sat_fm_restart_options                ""
% 1.68/0.96  --sat_gr_def                            false
% 1.68/0.96  --sat_epr_types                         true
% 1.68/0.96  --sat_non_cyclic_types                  false
% 1.68/0.96  --sat_finite_models                     false
% 1.68/0.96  --sat_fm_lemmas                         false
% 1.68/0.96  --sat_fm_prep                           false
% 1.68/0.96  --sat_fm_uc_incr                        true
% 1.68/0.96  --sat_out_model                         small
% 1.68/0.96  --sat_out_clauses                       false
% 1.68/0.96  
% 1.68/0.96  ------ QBF Options
% 1.68/0.96  
% 1.68/0.96  --qbf_mode                              false
% 1.68/0.96  --qbf_elim_univ                         false
% 1.68/0.96  --qbf_dom_inst                          none
% 1.68/0.96  --qbf_dom_pre_inst                      false
% 1.68/0.96  --qbf_sk_in                             false
% 1.68/0.96  --qbf_pred_elim                         true
% 1.68/0.96  --qbf_split                             512
% 1.68/0.96  
% 1.68/0.96  ------ BMC1 Options
% 1.68/0.96  
% 1.68/0.96  --bmc1_incremental                      false
% 1.68/0.96  --bmc1_axioms                           reachable_all
% 1.68/0.96  --bmc1_min_bound                        0
% 1.68/0.96  --bmc1_max_bound                        -1
% 1.68/0.96  --bmc1_max_bound_default                -1
% 1.68/0.96  --bmc1_symbol_reachability              true
% 1.68/0.96  --bmc1_property_lemmas                  false
% 1.68/0.96  --bmc1_k_induction                      false
% 1.68/0.96  --bmc1_non_equiv_states                 false
% 1.68/0.96  --bmc1_deadlock                         false
% 1.68/0.96  --bmc1_ucm                              false
% 1.68/0.96  --bmc1_add_unsat_core                   none
% 1.68/0.96  --bmc1_unsat_core_children              false
% 1.68/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.68/0.96  --bmc1_out_stat                         full
% 1.68/0.96  --bmc1_ground_init                      false
% 1.68/0.96  --bmc1_pre_inst_next_state              false
% 1.68/0.96  --bmc1_pre_inst_state                   false
% 1.68/0.96  --bmc1_pre_inst_reach_state             false
% 1.68/0.96  --bmc1_out_unsat_core                   false
% 1.68/0.96  --bmc1_aig_witness_out                  false
% 1.68/0.96  --bmc1_verbose                          false
% 1.68/0.96  --bmc1_dump_clauses_tptp                false
% 1.68/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.68/0.96  --bmc1_dump_file                        -
% 1.68/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.68/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.68/0.96  --bmc1_ucm_extend_mode                  1
% 1.68/0.96  --bmc1_ucm_init_mode                    2
% 1.68/0.96  --bmc1_ucm_cone_mode                    none
% 1.68/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.68/0.96  --bmc1_ucm_relax_model                  4
% 1.68/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.68/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.68/0.96  --bmc1_ucm_layered_model                none
% 1.68/0.96  --bmc1_ucm_max_lemma_size               10
% 1.68/0.96  
% 1.68/0.96  ------ AIG Options
% 1.68/0.96  
% 1.68/0.96  --aig_mode                              false
% 1.68/0.96  
% 1.68/0.96  ------ Instantiation Options
% 1.68/0.96  
% 1.68/0.96  --instantiation_flag                    true
% 1.68/0.96  --inst_sos_flag                         false
% 1.68/0.96  --inst_sos_phase                        true
% 1.68/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.68/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.68/0.96  --inst_lit_sel_side                     num_symb
% 1.68/0.96  --inst_solver_per_active                1400
% 1.68/0.96  --inst_solver_calls_frac                1.
% 1.68/0.96  --inst_passive_queue_type               priority_queues
% 1.68/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.68/0.96  --inst_passive_queues_freq              [25;2]
% 1.68/0.96  --inst_dismatching                      true
% 1.68/0.96  --inst_eager_unprocessed_to_passive     true
% 1.68/0.96  --inst_prop_sim_given                   true
% 1.68/0.96  --inst_prop_sim_new                     false
% 1.68/0.96  --inst_subs_new                         false
% 1.68/0.96  --inst_eq_res_simp                      false
% 1.68/0.96  --inst_subs_given                       false
% 1.68/0.96  --inst_orphan_elimination               true
% 1.68/0.96  --inst_learning_loop_flag               true
% 1.68/0.96  --inst_learning_start                   3000
% 1.68/0.96  --inst_learning_factor                  2
% 1.68/0.96  --inst_start_prop_sim_after_learn       3
% 1.68/0.96  --inst_sel_renew                        solver
% 1.68/0.96  --inst_lit_activity_flag                true
% 1.68/0.96  --inst_restr_to_given                   false
% 1.68/0.96  --inst_activity_threshold               500
% 1.68/0.96  --inst_out_proof                        true
% 1.68/0.96  
% 1.68/0.96  ------ Resolution Options
% 1.68/0.96  
% 1.68/0.96  --resolution_flag                       true
% 1.68/0.96  --res_lit_sel                           adaptive
% 1.68/0.96  --res_lit_sel_side                      none
% 1.68/0.96  --res_ordering                          kbo
% 1.68/0.96  --res_to_prop_solver                    active
% 1.68/0.96  --res_prop_simpl_new                    false
% 1.68/0.96  --res_prop_simpl_given                  true
% 1.68/0.96  --res_passive_queue_type                priority_queues
% 1.68/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.68/0.96  --res_passive_queues_freq               [15;5]
% 1.68/0.96  --res_forward_subs                      full
% 1.68/0.96  --res_backward_subs                     full
% 1.68/0.96  --res_forward_subs_resolution           true
% 1.68/0.96  --res_backward_subs_resolution          true
% 1.68/0.96  --res_orphan_elimination                true
% 1.68/0.96  --res_time_limit                        2.
% 1.68/0.96  --res_out_proof                         true
% 1.68/0.96  
% 1.68/0.96  ------ Superposition Options
% 1.68/0.96  
% 1.68/0.96  --superposition_flag                    true
% 1.68/0.96  --sup_passive_queue_type                priority_queues
% 1.68/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.68/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.68/0.96  --demod_completeness_check              fast
% 1.68/0.96  --demod_use_ground                      true
% 1.68/0.96  --sup_to_prop_solver                    passive
% 1.68/0.96  --sup_prop_simpl_new                    true
% 1.68/0.96  --sup_prop_simpl_given                  true
% 1.68/0.96  --sup_fun_splitting                     false
% 1.68/0.96  --sup_smt_interval                      50000
% 1.68/0.96  
% 1.68/0.96  ------ Superposition Simplification Setup
% 1.68/0.96  
% 1.68/0.96  --sup_indices_passive                   []
% 1.68/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.68/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.96  --sup_full_bw                           [BwDemod]
% 1.68/0.96  --sup_immed_triv                        [TrivRules]
% 1.68/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.68/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.96  --sup_immed_bw_main                     []
% 1.68/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.68/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/0.96  
% 1.68/0.96  ------ Combination Options
% 1.68/0.96  
% 1.68/0.96  --comb_res_mult                         3
% 1.68/0.96  --comb_sup_mult                         2
% 1.68/0.96  --comb_inst_mult                        10
% 1.68/0.96  
% 1.68/0.96  ------ Debug Options
% 1.68/0.96  
% 1.68/0.96  --dbg_backtrace                         false
% 1.68/0.96  --dbg_dump_prop_clauses                 false
% 1.68/0.96  --dbg_dump_prop_clauses_file            -
% 1.68/0.96  --dbg_out_stat                          false
% 1.68/0.96  ------ Parsing...
% 1.68/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.68/0.96  
% 1.68/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 1.68/0.96  
% 1.68/0.96  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.68/0.96  
% 1.68/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.68/0.96  ------ Proving...
% 1.68/0.96  ------ Problem Properties 
% 1.68/0.96  
% 1.68/0.96  
% 1.68/0.96  clauses                                 28
% 1.68/0.96  conjectures                             6
% 1.68/0.96  EPR                                     4
% 1.68/0.96  Horn                                    26
% 1.68/0.96  unary                                   6
% 1.68/0.96  binary                                  9
% 1.68/0.96  lits                                    70
% 1.68/0.96  lits eq                                 6
% 1.68/0.96  fd_pure                                 0
% 1.68/0.96  fd_pseudo                               0
% 1.68/0.96  fd_cond                                 0
% 1.68/0.96  fd_pseudo_cond                          1
% 1.68/0.96  AC symbols                              0
% 1.68/0.96  
% 1.68/0.96  ------ Schedule dynamic 5 is on 
% 1.68/0.96  
% 1.68/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.68/0.96  
% 1.68/0.96  
% 1.68/0.96  ------ 
% 1.68/0.96  Current options:
% 1.68/0.96  ------ 
% 1.68/0.96  
% 1.68/0.96  ------ Input Options
% 1.68/0.96  
% 1.68/0.96  --out_options                           all
% 1.68/0.96  --tptp_safe_out                         true
% 1.68/0.96  --problem_path                          ""
% 1.68/0.96  --include_path                          ""
% 1.68/0.96  --clausifier                            res/vclausify_rel
% 1.68/0.96  --clausifier_options                    --mode clausify
% 1.68/0.96  --stdin                                 false
% 1.68/0.96  --stats_out                             all
% 1.68/0.96  
% 1.68/0.96  ------ General Options
% 1.68/0.96  
% 1.68/0.96  --fof                                   false
% 1.68/0.96  --time_out_real                         305.
% 1.68/0.96  --time_out_virtual                      -1.
% 1.68/0.96  --symbol_type_check                     false
% 1.68/0.96  --clausify_out                          false
% 1.68/0.96  --sig_cnt_out                           false
% 1.68/0.96  --trig_cnt_out                          false
% 1.68/0.96  --trig_cnt_out_tolerance                1.
% 1.68/0.96  --trig_cnt_out_sk_spl                   false
% 1.68/0.96  --abstr_cl_out                          false
% 1.68/0.96  
% 1.68/0.96  ------ Global Options
% 1.68/0.96  
% 1.68/0.96  --schedule                              default
% 1.68/0.96  --add_important_lit                     false
% 1.68/0.96  --prop_solver_per_cl                    1000
% 1.68/0.96  --min_unsat_core                        false
% 1.68/0.96  --soft_assumptions                      false
% 1.68/0.96  --soft_lemma_size                       3
% 1.68/0.96  --prop_impl_unit_size                   0
% 1.68/0.96  --prop_impl_unit                        []
% 1.68/0.96  --share_sel_clauses                     true
% 1.68/0.96  --reset_solvers                         false
% 1.68/0.96  --bc_imp_inh                            [conj_cone]
% 1.68/0.96  --conj_cone_tolerance                   3.
% 1.68/0.96  --extra_neg_conj                        none
% 1.68/0.96  --large_theory_mode                     true
% 1.68/0.96  --prolific_symb_bound                   200
% 1.68/0.96  --lt_threshold                          2000
% 1.68/0.96  --clause_weak_htbl                      true
% 1.68/0.96  --gc_record_bc_elim                     false
% 1.68/0.96  
% 1.68/0.96  ------ Preprocessing Options
% 1.68/0.96  
% 1.68/0.96  --preprocessing_flag                    true
% 1.68/0.96  --time_out_prep_mult                    0.1
% 1.68/0.96  --splitting_mode                        input
% 1.68/0.96  --splitting_grd                         true
% 1.68/0.96  --splitting_cvd                         false
% 1.68/0.96  --splitting_cvd_svl                     false
% 1.68/0.96  --splitting_nvd                         32
% 1.68/0.96  --sub_typing                            true
% 1.68/0.96  --prep_gs_sim                           true
% 1.68/0.96  --prep_unflatten                        true
% 1.68/0.96  --prep_res_sim                          true
% 1.68/0.96  --prep_upred                            true
% 1.68/0.96  --prep_sem_filter                       exhaustive
% 1.68/0.96  --prep_sem_filter_out                   false
% 1.68/0.96  --pred_elim                             true
% 1.68/0.96  --res_sim_input                         true
% 1.68/0.96  --eq_ax_congr_red                       true
% 1.68/0.96  --pure_diseq_elim                       true
% 1.68/0.96  --brand_transform                       false
% 1.68/0.96  --non_eq_to_eq                          false
% 1.68/0.96  --prep_def_merge                        true
% 1.68/0.96  --prep_def_merge_prop_impl              false
% 1.68/0.96  --prep_def_merge_mbd                    true
% 1.68/0.96  --prep_def_merge_tr_red                 false
% 1.68/0.96  --prep_def_merge_tr_cl                  false
% 1.68/0.96  --smt_preprocessing                     true
% 1.68/0.96  --smt_ac_axioms                         fast
% 1.68/0.96  --preprocessed_out                      false
% 1.68/0.96  --preprocessed_stats                    false
% 1.68/0.96  
% 1.68/0.96  ------ Abstraction refinement Options
% 1.68/0.96  
% 1.68/0.96  --abstr_ref                             []
% 1.68/0.96  --abstr_ref_prep                        false
% 1.68/0.96  --abstr_ref_until_sat                   false
% 1.68/0.96  --abstr_ref_sig_restrict                funpre
% 1.68/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.68/0.96  --abstr_ref_under                       []
% 1.68/0.96  
% 1.68/0.96  ------ SAT Options
% 1.68/0.96  
% 1.68/0.96  --sat_mode                              false
% 1.68/0.96  --sat_fm_restart_options                ""
% 1.68/0.96  --sat_gr_def                            false
% 1.68/0.96  --sat_epr_types                         true
% 1.68/0.96  --sat_non_cyclic_types                  false
% 1.68/0.96  --sat_finite_models                     false
% 1.68/0.96  --sat_fm_lemmas                         false
% 1.68/0.96  --sat_fm_prep                           false
% 1.68/0.96  --sat_fm_uc_incr                        true
% 1.68/0.96  --sat_out_model                         small
% 1.68/0.96  --sat_out_clauses                       false
% 1.68/0.96  
% 1.68/0.96  ------ QBF Options
% 1.68/0.96  
% 1.68/0.96  --qbf_mode                              false
% 1.68/0.96  --qbf_elim_univ                         false
% 1.68/0.96  --qbf_dom_inst                          none
% 1.68/0.96  --qbf_dom_pre_inst                      false
% 1.68/0.96  --qbf_sk_in                             false
% 1.68/0.96  --qbf_pred_elim                         true
% 1.68/0.96  --qbf_split                             512
% 1.68/0.96  
% 1.68/0.96  ------ BMC1 Options
% 1.68/0.96  
% 1.68/0.96  --bmc1_incremental                      false
% 1.68/0.96  --bmc1_axioms                           reachable_all
% 1.68/0.96  --bmc1_min_bound                        0
% 1.68/0.96  --bmc1_max_bound                        -1
% 1.68/0.96  --bmc1_max_bound_default                -1
% 1.68/0.96  --bmc1_symbol_reachability              true
% 1.68/0.96  --bmc1_property_lemmas                  false
% 1.68/0.96  --bmc1_k_induction                      false
% 1.68/0.96  --bmc1_non_equiv_states                 false
% 1.68/0.96  --bmc1_deadlock                         false
% 1.68/0.96  --bmc1_ucm                              false
% 1.68/0.96  --bmc1_add_unsat_core                   none
% 1.68/0.96  --bmc1_unsat_core_children              false
% 1.68/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.68/0.96  --bmc1_out_stat                         full
% 1.68/0.96  --bmc1_ground_init                      false
% 1.68/0.96  --bmc1_pre_inst_next_state              false
% 1.68/0.96  --bmc1_pre_inst_state                   false
% 1.68/0.96  --bmc1_pre_inst_reach_state             false
% 1.68/0.96  --bmc1_out_unsat_core                   false
% 1.68/0.96  --bmc1_aig_witness_out                  false
% 1.68/0.96  --bmc1_verbose                          false
% 1.68/0.96  --bmc1_dump_clauses_tptp                false
% 1.68/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.68/0.96  --bmc1_dump_file                        -
% 1.68/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.68/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.68/0.96  --bmc1_ucm_extend_mode                  1
% 1.68/0.96  --bmc1_ucm_init_mode                    2
% 1.68/0.96  --bmc1_ucm_cone_mode                    none
% 1.68/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.68/0.96  --bmc1_ucm_relax_model                  4
% 1.68/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.68/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.68/0.96  --bmc1_ucm_layered_model                none
% 1.68/0.96  --bmc1_ucm_max_lemma_size               10
% 1.68/0.96  
% 1.68/0.96  ------ AIG Options
% 1.68/0.96  
% 1.68/0.96  --aig_mode                              false
% 1.68/0.96  
% 1.68/0.96  ------ Instantiation Options
% 1.68/0.96  
% 1.68/0.96  --instantiation_flag                    true
% 1.68/0.96  --inst_sos_flag                         false
% 1.68/0.96  --inst_sos_phase                        true
% 1.68/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.68/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.68/0.96  --inst_lit_sel_side                     none
% 1.68/0.96  --inst_solver_per_active                1400
% 1.68/0.96  --inst_solver_calls_frac                1.
% 1.68/0.96  --inst_passive_queue_type               priority_queues
% 1.68/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.68/0.96  --inst_passive_queues_freq              [25;2]
% 1.68/0.96  --inst_dismatching                      true
% 1.68/0.96  --inst_eager_unprocessed_to_passive     true
% 1.68/0.96  --inst_prop_sim_given                   true
% 1.68/0.96  --inst_prop_sim_new                     false
% 1.68/0.96  --inst_subs_new                         false
% 1.68/0.96  --inst_eq_res_simp                      false
% 1.68/0.96  --inst_subs_given                       false
% 1.68/0.96  --inst_orphan_elimination               true
% 1.68/0.96  --inst_learning_loop_flag               true
% 1.68/0.96  --inst_learning_start                   3000
% 1.68/0.96  --inst_learning_factor                  2
% 1.68/0.96  --inst_start_prop_sim_after_learn       3
% 1.68/0.96  --inst_sel_renew                        solver
% 1.68/0.96  --inst_lit_activity_flag                true
% 1.68/0.96  --inst_restr_to_given                   false
% 1.68/0.96  --inst_activity_threshold               500
% 1.68/0.96  --inst_out_proof                        true
% 1.68/0.96  
% 1.68/0.96  ------ Resolution Options
% 1.68/0.96  
% 1.68/0.96  --resolution_flag                       false
% 1.68/0.96  --res_lit_sel                           adaptive
% 1.68/0.96  --res_lit_sel_side                      none
% 1.68/0.96  --res_ordering                          kbo
% 1.68/0.96  --res_to_prop_solver                    active
% 1.68/0.96  --res_prop_simpl_new                    false
% 1.68/0.96  --res_prop_simpl_given                  true
% 1.68/0.96  --res_passive_queue_type                priority_queues
% 1.68/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.68/0.96  --res_passive_queues_freq               [15;5]
% 1.68/0.96  --res_forward_subs                      full
% 1.68/0.96  --res_backward_subs                     full
% 1.68/0.96  --res_forward_subs_resolution           true
% 1.68/0.96  --res_backward_subs_resolution          true
% 1.68/0.96  --res_orphan_elimination                true
% 1.68/0.96  --res_time_limit                        2.
% 1.68/0.96  --res_out_proof                         true
% 1.68/0.96  
% 1.68/0.96  ------ Superposition Options
% 1.68/0.96  
% 1.68/0.96  --superposition_flag                    true
% 1.68/0.96  --sup_passive_queue_type                priority_queues
% 1.68/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.68/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.68/0.96  --demod_completeness_check              fast
% 1.68/0.96  --demod_use_ground                      true
% 1.68/0.96  --sup_to_prop_solver                    passive
% 1.68/0.96  --sup_prop_simpl_new                    true
% 1.68/0.96  --sup_prop_simpl_given                  true
% 1.68/0.96  --sup_fun_splitting                     false
% 1.68/0.96  --sup_smt_interval                      50000
% 1.68/0.96  
% 1.68/0.96  ------ Superposition Simplification Setup
% 1.68/0.96  
% 1.68/0.96  --sup_indices_passive                   []
% 1.68/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.68/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.96  --sup_full_bw                           [BwDemod]
% 1.68/0.96  --sup_immed_triv                        [TrivRules]
% 1.68/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.68/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.96  --sup_immed_bw_main                     []
% 1.68/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.68/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/0.96  
% 1.68/0.96  ------ Combination Options
% 1.68/0.96  
% 1.68/0.96  --comb_res_mult                         3
% 1.68/0.96  --comb_sup_mult                         2
% 1.68/0.96  --comb_inst_mult                        10
% 1.68/0.96  
% 1.68/0.96  ------ Debug Options
% 1.68/0.96  
% 1.68/0.96  --dbg_backtrace                         false
% 1.68/0.96  --dbg_dump_prop_clauses                 false
% 1.68/0.96  --dbg_dump_prop_clauses_file            -
% 1.68/0.96  --dbg_out_stat                          false
% 1.68/0.96  
% 1.68/0.96  
% 1.68/0.96  
% 1.68/0.96  
% 1.68/0.96  ------ Proving...
% 1.68/0.96  
% 1.68/0.96  
% 1.68/0.96  % SZS status Theorem for theBenchmark.p
% 1.68/0.96  
% 1.68/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 1.68/0.96  
% 1.68/0.96  fof(f3,axiom,(
% 1.68/0.96    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.68/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.96  
% 1.68/0.96  fof(f18,plain,(
% 1.68/0.96    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.68/0.96    inference(ennf_transformation,[],[f3])).
% 1.68/0.96  
% 1.68/0.96  fof(f59,plain,(
% 1.68/0.96    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.68/0.96    inference(cnf_transformation,[],[f18])).
% 1.68/0.96  
% 1.68/0.96  fof(f14,conjecture,(
% 1.68/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.68/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.96  
% 1.68/0.96  fof(f15,negated_conjecture,(
% 1.68/0.96    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.68/0.96    inference(negated_conjecture,[],[f14])).
% 1.68/0.96  
% 1.68/0.96  fof(f37,plain,(
% 1.68/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.68/0.96    inference(ennf_transformation,[],[f15])).
% 1.68/0.96  
% 1.68/0.96  fof(f38,plain,(
% 1.68/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.68/0.96    inference(flattening,[],[f37])).
% 1.68/0.96  
% 1.68/0.96  fof(f46,plain,(
% 1.68/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.68/0.96    inference(nnf_transformation,[],[f38])).
% 1.68/0.96  
% 1.68/0.96  fof(f47,plain,(
% 1.68/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.68/0.96    inference(flattening,[],[f46])).
% 1.68/0.96  
% 1.68/0.96  fof(f53,plain,(
% 1.68/0.96    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6) | r1_tmap_1(X1,X0,X2,X4)) & sK6 = X4 & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 1.68/0.96    introduced(choice_axiom,[])).
% 1.68/0.96  
% 1.68/0.96  fof(f52,plain,(
% 1.68/0.96    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK5)) & sK5 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK5,u1_struct_0(X1)))) )),
% 1.68/0.96    introduced(choice_axiom,[])).
% 1.68/0.96  
% 1.68/0.96  fof(f51,plain,(
% 1.68/0.96    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK4,X1) & v1_tsep_1(sK4,X1) & ~v2_struct_0(sK4))) )),
% 1.68/0.96    introduced(choice_axiom,[])).
% 1.68/0.96  
% 1.68/0.96  fof(f50,plain,(
% 1.68/0.96    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X5) | ~r1_tmap_1(X1,X0,sK3,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X5) | r1_tmap_1(X1,X0,sK3,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 1.68/0.96    introduced(choice_axiom,[])).
% 1.68/0.96  
% 1.68/0.96  fof(f49,plain,(
% 1.68/0.96    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X5) | ~r1_tmap_1(sK2,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X5) | r1_tmap_1(sK2,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK2))) & m1_pre_topc(X3,sK2) & v1_tsep_1(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 1.68/0.96    introduced(choice_axiom,[])).
% 1.68/0.96  
% 1.68/0.96  fof(f48,plain,(
% 1.68/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X5) | ~r1_tmap_1(X1,sK1,X2,X4)) & (r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X5) | r1_tmap_1(X1,sK1,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.68/0.96    introduced(choice_axiom,[])).
% 1.68/0.96  
% 1.68/0.96  fof(f54,plain,(
% 1.68/0.96    ((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | ~r1_tmap_1(sK2,sK1,sK3,sK5)) & (r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | r1_tmap_1(sK2,sK1,sK3,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK2))) & m1_pre_topc(sK4,sK2) & v1_tsep_1(sK4,sK2) & ~v2_struct_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.68/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f47,f53,f52,f51,f50,f49,f48])).
% 1.68/0.96  
% 1.68/0.96  fof(f89,plain,(
% 1.68/0.96    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | ~r1_tmap_1(sK2,sK1,sK3,sK5)),
% 1.68/0.96    inference(cnf_transformation,[],[f54])).
% 1.68/0.96  
% 1.68/0.96  fof(f87,plain,(
% 1.68/0.96    sK5 = sK6),
% 1.68/0.96    inference(cnf_transformation,[],[f54])).
% 1.68/0.96  
% 1.68/0.96  fof(f86,plain,(
% 1.68/0.96    m1_subset_1(sK6,u1_struct_0(sK4))),
% 1.68/0.96    inference(cnf_transformation,[],[f54])).
% 1.68/0.96  
% 1.68/0.96  fof(f84,plain,(
% 1.68/0.96    m1_pre_topc(sK4,sK2)),
% 1.68/0.96    inference(cnf_transformation,[],[f54])).
% 1.68/0.96  
% 1.68/0.96  fof(f13,axiom,(
% 1.68/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.68/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.96  
% 1.68/0.96  fof(f35,plain,(
% 1.68/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.68/0.96    inference(ennf_transformation,[],[f13])).
% 1.68/0.96  
% 1.68/0.96  fof(f36,plain,(
% 1.68/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.68/0.96    inference(flattening,[],[f35])).
% 1.68/0.96  
% 1.68/0.96  fof(f45,plain,(
% 1.68/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.68/0.97    inference(nnf_transformation,[],[f36])).
% 1.68/0.97  
% 1.68/0.97  fof(f71,plain,(
% 1.68/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.97    inference(cnf_transformation,[],[f45])).
% 1.68/0.97  
% 1.68/0.97  fof(f97,plain,(
% 1.68/0.97    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.97    inference(equality_resolution,[],[f71])).
% 1.68/0.97  
% 1.68/0.97  fof(f12,axiom,(
% 1.68/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 1.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.97  
% 1.68/0.97  fof(f33,plain,(
% 1.68/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.68/0.97    inference(ennf_transformation,[],[f12])).
% 1.68/0.97  
% 1.68/0.97  fof(f34,plain,(
% 1.68/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.68/0.97    inference(flattening,[],[f33])).
% 1.68/0.97  
% 1.68/0.97  fof(f70,plain,(
% 1.68/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.97    inference(cnf_transformation,[],[f34])).
% 1.68/0.97  
% 1.68/0.97  fof(f95,plain,(
% 1.68/0.97    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.97    inference(equality_resolution,[],[f70])).
% 1.68/0.97  
% 1.68/0.97  fof(f80,plain,(
% 1.68/0.97    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.68/0.97    inference(cnf_transformation,[],[f54])).
% 1.68/0.97  
% 1.68/0.97  fof(f79,plain,(
% 1.68/0.97    v1_funct_1(sK3)),
% 1.68/0.97    inference(cnf_transformation,[],[f54])).
% 1.68/0.97  
% 1.68/0.97  fof(f6,axiom,(
% 1.68/0.97    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.97  
% 1.68/0.97  fof(f22,plain,(
% 1.68/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.68/0.97    inference(ennf_transformation,[],[f6])).
% 1.68/0.97  
% 1.68/0.97  fof(f23,plain,(
% 1.68/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.68/0.97    inference(flattening,[],[f22])).
% 1.68/0.97  
% 1.68/0.97  fof(f62,plain,(
% 1.68/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.97    inference(cnf_transformation,[],[f23])).
% 1.68/0.97  
% 1.68/0.97  fof(f76,plain,(
% 1.68/0.97    ~v2_struct_0(sK2)),
% 1.68/0.97    inference(cnf_transformation,[],[f54])).
% 1.68/0.97  
% 1.68/0.97  fof(f77,plain,(
% 1.68/0.97    v2_pre_topc(sK2)),
% 1.68/0.97    inference(cnf_transformation,[],[f54])).
% 1.68/0.97  
% 1.68/0.97  fof(f78,plain,(
% 1.68/0.97    l1_pre_topc(sK2)),
% 1.68/0.97    inference(cnf_transformation,[],[f54])).
% 1.68/0.97  
% 1.68/0.97  fof(f82,plain,(
% 1.68/0.97    ~v2_struct_0(sK4)),
% 1.68/0.97    inference(cnf_transformation,[],[f54])).
% 1.68/0.97  
% 1.68/0.97  fof(f74,plain,(
% 1.68/0.97    v2_pre_topc(sK1)),
% 1.68/0.97    inference(cnf_transformation,[],[f54])).
% 1.68/0.97  
% 1.68/0.97  fof(f73,plain,(
% 1.68/0.97    ~v2_struct_0(sK1)),
% 1.68/0.97    inference(cnf_transformation,[],[f54])).
% 1.68/0.97  
% 1.68/0.97  fof(f75,plain,(
% 1.68/0.97    l1_pre_topc(sK1)),
% 1.68/0.97    inference(cnf_transformation,[],[f54])).
% 1.68/0.97  
% 1.68/0.97  fof(f81,plain,(
% 1.68/0.97    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.68/0.97    inference(cnf_transformation,[],[f54])).
% 1.68/0.97  
% 1.68/0.97  fof(f2,axiom,(
% 1.68/0.97    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.97  
% 1.68/0.97  fof(f16,plain,(
% 1.68/0.97    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.68/0.97    inference(ennf_transformation,[],[f2])).
% 1.68/0.97  
% 1.68/0.97  fof(f17,plain,(
% 1.68/0.97    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.68/0.97    inference(flattening,[],[f16])).
% 1.68/0.97  
% 1.68/0.97  fof(f58,plain,(
% 1.68/0.97    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.68/0.97    inference(cnf_transformation,[],[f17])).
% 1.68/0.97  
% 1.68/0.97  fof(f72,plain,(
% 1.68/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.97    inference(cnf_transformation,[],[f45])).
% 1.68/0.97  
% 1.68/0.97  fof(f96,plain,(
% 1.68/0.97    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.97    inference(equality_resolution,[],[f72])).
% 1.68/0.97  
% 1.68/0.97  fof(f10,axiom,(
% 1.68/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.97  
% 1.68/0.97  fof(f30,plain,(
% 1.68/0.97    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.68/0.97    inference(ennf_transformation,[],[f10])).
% 1.68/0.97  
% 1.68/0.97  fof(f31,plain,(
% 1.68/0.97    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.68/0.97    inference(flattening,[],[f30])).
% 1.68/0.97  
% 1.68/0.97  fof(f43,plain,(
% 1.68/0.97    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.68/0.97    inference(nnf_transformation,[],[f31])).
% 1.68/0.97  
% 1.68/0.97  fof(f44,plain,(
% 1.68/0.97    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.68/0.97    inference(flattening,[],[f43])).
% 1.68/0.97  
% 1.68/0.97  fof(f66,plain,(
% 1.68/0.97    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.68/0.97    inference(cnf_transformation,[],[f44])).
% 1.68/0.97  
% 1.68/0.97  fof(f94,plain,(
% 1.68/0.97    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.68/0.97    inference(equality_resolution,[],[f66])).
% 1.68/0.97  
% 1.68/0.97  fof(f11,axiom,(
% 1.68/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.97  
% 1.68/0.97  fof(f32,plain,(
% 1.68/0.97    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.68/0.97    inference(ennf_transformation,[],[f11])).
% 1.68/0.97  
% 1.68/0.97  fof(f69,plain,(
% 1.68/0.97    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.68/0.97    inference(cnf_transformation,[],[f32])).
% 1.68/0.97  
% 1.68/0.97  fof(f83,plain,(
% 1.68/0.97    v1_tsep_1(sK4,sK2)),
% 1.68/0.97    inference(cnf_transformation,[],[f54])).
% 1.68/0.97  
% 1.68/0.97  fof(f1,axiom,(
% 1.68/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.97  
% 1.68/0.97  fof(f39,plain,(
% 1.68/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.68/0.97    inference(nnf_transformation,[],[f1])).
% 1.68/0.97  
% 1.68/0.97  fof(f40,plain,(
% 1.68/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.68/0.97    inference(flattening,[],[f39])).
% 1.68/0.97  
% 1.68/0.97  fof(f56,plain,(
% 1.68/0.97    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.68/0.97    inference(cnf_transformation,[],[f40])).
% 1.68/0.97  
% 1.68/0.97  fof(f90,plain,(
% 1.68/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.68/0.97    inference(equality_resolution,[],[f56])).
% 1.68/0.97  
% 1.68/0.97  fof(f9,axiom,(
% 1.68/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 1.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.97  
% 1.68/0.97  fof(f28,plain,(
% 1.68/0.97    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.68/0.97    inference(ennf_transformation,[],[f9])).
% 1.68/0.97  
% 1.68/0.97  fof(f29,plain,(
% 1.68/0.97    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.68/0.97    inference(flattening,[],[f28])).
% 1.68/0.97  
% 1.68/0.97  fof(f65,plain,(
% 1.68/0.97    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.97    inference(cnf_transformation,[],[f29])).
% 1.68/0.97  
% 1.68/0.97  fof(f7,axiom,(
% 1.68/0.97    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.97  
% 1.68/0.97  fof(f24,plain,(
% 1.68/0.97    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.68/0.97    inference(ennf_transformation,[],[f7])).
% 1.68/0.97  
% 1.68/0.97  fof(f25,plain,(
% 1.68/0.97    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.68/0.97    inference(flattening,[],[f24])).
% 1.68/0.97  
% 1.68/0.97  fof(f63,plain,(
% 1.68/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.97    inference(cnf_transformation,[],[f25])).
% 1.68/0.97  
% 1.68/0.97  fof(f8,axiom,(
% 1.68/0.97    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 1.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.97  
% 1.68/0.97  fof(f26,plain,(
% 1.68/0.97    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.68/0.97    inference(ennf_transformation,[],[f8])).
% 1.68/0.97  
% 1.68/0.97  fof(f27,plain,(
% 1.68/0.97    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.68/0.97    inference(flattening,[],[f26])).
% 1.68/0.97  
% 1.68/0.97  fof(f41,plain,(
% 1.68/0.97    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK0(X0,X1),X0,X1))),
% 1.68/0.97    introduced(choice_axiom,[])).
% 1.68/0.97  
% 1.68/0.97  fof(f42,plain,(
% 1.68/0.97    ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.68/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f41])).
% 1.68/0.97  
% 1.68/0.97  fof(f64,plain,(
% 1.68/0.97    ( ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.97    inference(cnf_transformation,[],[f42])).
% 1.68/0.97  
% 1.68/0.97  fof(f4,axiom,(
% 1.68/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.97  
% 1.68/0.97  fof(f19,plain,(
% 1.68/0.97    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.68/0.97    inference(ennf_transformation,[],[f4])).
% 1.68/0.97  
% 1.68/0.97  fof(f20,plain,(
% 1.68/0.97    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.68/0.97    inference(flattening,[],[f19])).
% 1.68/0.97  
% 1.68/0.97  fof(f60,plain,(
% 1.68/0.97    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.68/0.97    inference(cnf_transformation,[],[f20])).
% 1.68/0.97  
% 1.68/0.97  fof(f5,axiom,(
% 1.68/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.97  
% 1.68/0.97  fof(f21,plain,(
% 1.68/0.97    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.68/0.97    inference(ennf_transformation,[],[f5])).
% 1.68/0.97  
% 1.68/0.97  fof(f61,plain,(
% 1.68/0.97    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.68/0.97    inference(cnf_transformation,[],[f21])).
% 1.68/0.97  
% 1.68/0.97  fof(f88,plain,(
% 1.68/0.97    r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | r1_tmap_1(sK2,sK1,sK3,sK5)),
% 1.68/0.97    inference(cnf_transformation,[],[f54])).
% 1.68/0.97  
% 1.68/0.97  cnf(c_4,plain,
% 1.68/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.68/0.97      | ~ r2_hidden(X2,X0)
% 1.68/0.97      | ~ v1_xboole_0(X1) ),
% 1.68/0.97      inference(cnf_transformation,[],[f59]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_3439,plain,
% 1.68/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.68/0.97      | ~ r2_hidden(X1,X0)
% 1.68/0.97      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 1.68/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_3676,plain,
% 1.68/0.97      ( ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.68/0.97      | ~ r2_hidden(X0,sK0(sK4,sK6))
% 1.68/0.97      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 1.68/0.97      inference(instantiation,[status(thm)],[c_3439]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_3840,plain,
% 1.68/0.97      ( ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.68/0.97      | ~ r2_hidden(sK6,sK0(sK4,sK6))
% 1.68/0.97      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 1.68/0.97      inference(instantiation,[status(thm)],[c_3676]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_18,negated_conjecture,
% 1.68/0.97      ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
% 1.68/0.97      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 1.68/0.97      inference(cnf_transformation,[],[f89]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_3098,plain,
% 1.68/0.97      ( r1_tmap_1(sK2,sK1,sK3,sK5) != iProver_top
% 1.68/0.97      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
% 1.68/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_20,negated_conjecture,
% 1.68/0.97      ( sK5 = sK6 ),
% 1.68/0.97      inference(cnf_transformation,[],[f87]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_3167,plain,
% 1.68/0.97      ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
% 1.68/0.97      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
% 1.68/0.97      inference(light_normalisation,[status(thm)],[c_3098,c_20]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_21,negated_conjecture,
% 1.68/0.97      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.68/0.97      inference(cnf_transformation,[],[f86]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_48,plain,
% 1.68/0.97      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 1.68/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_23,negated_conjecture,
% 1.68/0.97      ( m1_pre_topc(sK4,sK2) ),
% 1.68/0.97      inference(cnf_transformation,[],[f84]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_17,plain,
% 1.68/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.68/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.68/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.68/0.97      | ~ v3_pre_topc(X5,X0)
% 1.68/0.97      | ~ m1_pre_topc(X4,X0)
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.68/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.68/0.97      | ~ r2_hidden(X3,X5)
% 1.68/0.97      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.68/0.97      | ~ v1_funct_1(X2)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(X4)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ l1_pre_topc(X0)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X0) ),
% 1.68/0.97      inference(cnf_transformation,[],[f97]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_15,plain,
% 1.68/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.68/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.68/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.68/0.97      | ~ m1_pre_topc(X4,X0)
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.68/0.97      | ~ v1_funct_1(X2)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(X4)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ l1_pre_topc(X0)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X0) ),
% 1.68/0.97      inference(cnf_transformation,[],[f95]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_180,plain,
% 1.68/0.97      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.68/0.97      | ~ m1_pre_topc(X4,X0)
% 1.68/0.97      | ~ r1_tmap_1(X0,X1,X2,X3)
% 1.68/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.68/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.68/0.97      | ~ v1_funct_1(X2)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(X4)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ l1_pre_topc(X0)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X0) ),
% 1.68/0.97      inference(global_propositional_subsumption,
% 1.68/0.97                [status(thm)],
% 1.68/0.97                [c_17,c_15]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_181,plain,
% 1.68/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.68/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.68/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.68/0.97      | ~ m1_pre_topc(X4,X0)
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.68/0.97      | ~ v1_funct_1(X2)
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | v2_struct_0(X4)
% 1.68/0.97      | ~ l1_pre_topc(X0)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X0)
% 1.68/0.97      | ~ v2_pre_topc(X1) ),
% 1.68/0.97      inference(renaming,[status(thm)],[c_180]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_27,negated_conjecture,
% 1.68/0.97      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 1.68/0.97      inference(cnf_transformation,[],[f80]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_582,plain,
% 1.68/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.68/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.68/0.97      | ~ m1_pre_topc(X4,X0)
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.68/0.97      | ~ v1_funct_1(X2)
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | v2_struct_0(X4)
% 1.68/0.97      | ~ l1_pre_topc(X0)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X0)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.68/0.97      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.68/0.97      | sK3 != X2 ),
% 1.68/0.97      inference(resolution_lifted,[status(thm)],[c_181,c_27]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_583,plain,
% 1.68/0.97      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 1.68/0.97      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 1.68/0.97      | ~ m1_pre_topc(X0,X2)
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.68/0.97      | ~ v1_funct_1(sK3)
% 1.68/0.97      | v2_struct_0(X2)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | ~ l1_pre_topc(X2)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X2)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.68/0.97      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.68/0.97      inference(unflattening,[status(thm)],[c_582]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_28,negated_conjecture,
% 1.68/0.97      ( v1_funct_1(sK3) ),
% 1.68/0.97      inference(cnf_transformation,[],[f79]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_587,plain,
% 1.68/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_pre_topc(X0,X2)
% 1.68/0.97      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 1.68/0.97      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 1.68/0.97      | v2_struct_0(X2)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | ~ l1_pre_topc(X2)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X2)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.68/0.97      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.68/0.97      inference(global_propositional_subsumption,
% 1.68/0.97                [status(thm)],
% 1.68/0.97                [c_583,c_28]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_588,plain,
% 1.68/0.97      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 1.68/0.97      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 1.68/0.97      | ~ m1_pre_topc(X0,X2)
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | v2_struct_0(X2)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ l1_pre_topc(X2)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X2)
% 1.68/0.97      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.68/0.97      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.68/0.97      inference(renaming,[status(thm)],[c_587]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_7,plain,
% 1.68/0.97      ( ~ m1_pre_topc(X0,X1)
% 1.68/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.68/0.97      | m1_subset_1(X2,u1_struct_0(X1))
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | ~ l1_pre_topc(X1) ),
% 1.68/0.97      inference(cnf_transformation,[],[f62]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_623,plain,
% 1.68/0.97      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 1.68/0.97      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 1.68/0.97      | ~ m1_pre_topc(X0,X2)
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | v2_struct_0(X2)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ l1_pre_topc(X2)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X2)
% 1.68/0.97      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.68/0.97      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.68/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_588,c_7]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_795,plain,
% 1.68/0.97      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 1.68/0.97      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(X2)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | ~ l1_pre_topc(X2)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X2)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.68/0.97      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.68/0.97      | sK2 != X2
% 1.68/0.97      | sK4 != X0 ),
% 1.68/0.97      inference(resolution_lifted,[status(thm)],[c_23,c_623]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_796,plain,
% 1.68/0.97      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 1.68/0.97      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.68/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(sK2)
% 1.68/0.97      | v2_struct_0(sK4)
% 1.68/0.97      | ~ l1_pre_topc(X0)
% 1.68/0.97      | ~ l1_pre_topc(sK2)
% 1.68/0.97      | ~ v2_pre_topc(X0)
% 1.68/0.97      | ~ v2_pre_topc(sK2)
% 1.68/0.97      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.68/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.68/0.97      inference(unflattening,[status(thm)],[c_795]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_31,negated_conjecture,
% 1.68/0.97      ( ~ v2_struct_0(sK2) ),
% 1.68/0.97      inference(cnf_transformation,[],[f76]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_30,negated_conjecture,
% 1.68/0.97      ( v2_pre_topc(sK2) ),
% 1.68/0.97      inference(cnf_transformation,[],[f77]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_29,negated_conjecture,
% 1.68/0.97      ( l1_pre_topc(sK2) ),
% 1.68/0.97      inference(cnf_transformation,[],[f78]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_25,negated_conjecture,
% 1.68/0.97      ( ~ v2_struct_0(sK4) ),
% 1.68/0.97      inference(cnf_transformation,[],[f82]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_800,plain,
% 1.68/0.97      ( ~ v2_pre_topc(X0)
% 1.68/0.97      | ~ r1_tmap_1(sK2,X0,sK3,X1)
% 1.68/0.97      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.68/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | ~ l1_pre_topc(X0)
% 1.68/0.97      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.68/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.68/0.97      inference(global_propositional_subsumption,
% 1.68/0.97                [status(thm)],
% 1.68/0.97                [c_796,c_31,c_30,c_29,c_25]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_801,plain,
% 1.68/0.97      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 1.68/0.97      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.68/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | ~ l1_pre_topc(X0)
% 1.68/0.97      | ~ v2_pre_topc(X0)
% 1.68/0.97      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.68/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.68/0.97      inference(renaming,[status(thm)],[c_800]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_33,negated_conjecture,
% 1.68/0.97      ( v2_pre_topc(sK1) ),
% 1.68/0.97      inference(cnf_transformation,[],[f74]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_1130,plain,
% 1.68/0.97      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 1.68/0.97      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.68/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | ~ l1_pre_topc(X0)
% 1.68/0.97      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.68/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.68/0.97      | sK1 != X0 ),
% 1.68/0.97      inference(resolution_lifted,[status(thm)],[c_801,c_33]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_1131,plain,
% 1.68/0.97      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 1.68/0.97      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.68/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.68/0.97      | v2_struct_0(sK1)
% 1.68/0.97      | ~ l1_pre_topc(sK1)
% 1.68/0.97      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.68/0.97      inference(unflattening,[status(thm)],[c_1130]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_34,negated_conjecture,
% 1.68/0.97      ( ~ v2_struct_0(sK1) ),
% 1.68/0.97      inference(cnf_transformation,[],[f73]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_32,negated_conjecture,
% 1.68/0.97      ( l1_pre_topc(sK1) ),
% 1.68/0.97      inference(cnf_transformation,[],[f75]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_26,negated_conjecture,
% 1.68/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 1.68/0.97      inference(cnf_transformation,[],[f81]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_1135,plain,
% 1.68/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.68/0.97      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.68/0.97      | ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 1.68/0.97      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.68/0.97      inference(global_propositional_subsumption,
% 1.68/0.97                [status(thm)],
% 1.68/0.97                [c_1131,c_34,c_32,c_26]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_1136,plain,
% 1.68/0.97      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 1.68/0.97      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.68/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.68/0.97      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.68/0.97      inference(renaming,[status(thm)],[c_1135]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_1837,plain,
% 1.68/0.97      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 1.68/0.97      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.68/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 1.68/0.97      inference(equality_resolution_simp,[status(thm)],[c_1136]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_3325,plain,
% 1.68/0.97      ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
% 1.68/0.97      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 1.68/0.97      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.68/0.97      inference(instantiation,[status(thm)],[c_1837]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_3326,plain,
% 1.68/0.97      ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
% 1.68/0.97      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top
% 1.68/0.97      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 1.68/0.97      inference(predicate_to_equality,[status(thm)],[c_3325]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_3346,plain,
% 1.68/0.97      ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top ),
% 1.68/0.97      inference(global_propositional_subsumption,
% 1.68/0.97                [status(thm)],
% 1.68/0.97                [c_3167,c_48,c_3326]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_3348,plain,
% 1.68/0.97      ( ~ r1_tmap_1(sK2,sK1,sK3,sK6) ),
% 1.68/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_3346]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_3,plain,
% 1.68/0.97      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.68/0.97      inference(cnf_transformation,[],[f58]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_3331,plain,
% 1.68/0.97      ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 1.68/0.97      | r2_hidden(sK6,u1_struct_0(sK4))
% 1.68/0.97      | v1_xboole_0(u1_struct_0(sK4)) ),
% 1.68/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_16,plain,
% 1.68/0.97      ( r1_tmap_1(X0,X1,X2,X3)
% 1.68/0.97      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.68/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.68/0.97      | ~ v3_pre_topc(X5,X0)
% 1.68/0.97      | ~ m1_pre_topc(X4,X0)
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.68/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.68/0.97      | ~ r2_hidden(X3,X5)
% 1.68/0.97      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.68/0.97      | ~ v1_funct_1(X2)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(X4)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ l1_pre_topc(X0)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X0) ),
% 1.68/0.97      inference(cnf_transformation,[],[f96]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_13,plain,
% 1.68/0.97      ( ~ v1_tsep_1(X0,X1)
% 1.68/0.97      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.68/0.97      | ~ m1_pre_topc(X0,X1)
% 1.68/0.97      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X1) ),
% 1.68/0.97      inference(cnf_transformation,[],[f94]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_14,plain,
% 1.68/0.97      ( ~ m1_pre_topc(X0,X1)
% 1.68/0.97      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.97      | ~ l1_pre_topc(X1) ),
% 1.68/0.97      inference(cnf_transformation,[],[f69]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_188,plain,
% 1.68/0.97      ( ~ m1_pre_topc(X0,X1)
% 1.68/0.97      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.68/0.97      | ~ v1_tsep_1(X0,X1)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X1) ),
% 1.68/0.97      inference(global_propositional_subsumption,
% 1.68/0.97                [status(thm)],
% 1.68/0.97                [c_13,c_14]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_189,plain,
% 1.68/0.97      ( ~ v1_tsep_1(X0,X1)
% 1.68/0.97      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.68/0.97      | ~ m1_pre_topc(X0,X1)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X1) ),
% 1.68/0.97      inference(renaming,[status(thm)],[c_188]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_24,negated_conjecture,
% 1.68/0.97      ( v1_tsep_1(sK4,sK2) ),
% 1.68/0.97      inference(cnf_transformation,[],[f83]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_459,plain,
% 1.68/0.97      ( v3_pre_topc(u1_struct_0(X0),X1)
% 1.68/0.97      | ~ m1_pre_topc(X0,X1)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | sK2 != X1
% 1.68/0.97      | sK4 != X0 ),
% 1.68/0.97      inference(resolution_lifted,[status(thm)],[c_189,c_24]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_460,plain,
% 1.68/0.97      ( v3_pre_topc(u1_struct_0(sK4),sK2)
% 1.68/0.97      | ~ m1_pre_topc(sK4,sK2)
% 1.68/0.97      | ~ l1_pre_topc(sK2)
% 1.68/0.97      | ~ v2_pre_topc(sK2) ),
% 1.68/0.97      inference(unflattening,[status(thm)],[c_459]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_462,plain,
% 1.68/0.97      ( v3_pre_topc(u1_struct_0(sK4),sK2) ),
% 1.68/0.97      inference(global_propositional_subsumption,
% 1.68/0.97                [status(thm)],
% 1.68/0.97                [c_460,c_30,c_29,c_23]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_526,plain,
% 1.68/0.97      ( r1_tmap_1(X0,X1,X2,X3)
% 1.68/0.97      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.68/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.68/0.97      | ~ m1_pre_topc(X4,X0)
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.68/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.68/0.97      | ~ r2_hidden(X3,X5)
% 1.68/0.97      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.68/0.97      | ~ v1_funct_1(X2)
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | v2_struct_0(X4)
% 1.68/0.97      | ~ l1_pre_topc(X0)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X0)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | u1_struct_0(sK4) != X5
% 1.68/0.97      | sK2 != X0 ),
% 1.68/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_462]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_527,plain,
% 1.68/0.97      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,X2,X0),X3)
% 1.68/0.97      | r1_tmap_1(sK2,X1,X2,X3)
% 1.68/0.97      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
% 1.68/0.97      | ~ m1_pre_topc(X0,sK2)
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 1.68/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 1.68/0.97      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.97      | ~ r2_hidden(X3,u1_struct_0(sK4))
% 1.68/0.97      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 1.68/0.97      | ~ v1_funct_1(X2)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(sK2)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ l1_pre_topc(sK2)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(sK2) ),
% 1.68/0.97      inference(unflattening,[status(thm)],[c_526]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_531,plain,
% 1.68/0.97      ( ~ v2_pre_topc(X1)
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | ~ v1_funct_1(X2)
% 1.68/0.97      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 1.68/0.97      | ~ r2_hidden(X3,u1_struct_0(sK4))
% 1.68/0.97      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_pre_topc(X0,sK2)
% 1.68/0.97      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
% 1.68/0.97      | r1_tmap_1(sK2,X1,X2,X3)
% 1.68/0.97      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,X2,X0),X3)
% 1.68/0.97      | ~ l1_pre_topc(X1) ),
% 1.68/0.97      inference(global_propositional_subsumption,
% 1.68/0.97                [status(thm)],
% 1.68/0.97                [c_527,c_31,c_30,c_29]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_532,plain,
% 1.68/0.97      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,X2,X0),X3)
% 1.68/0.97      | r1_tmap_1(sK2,X1,X2,X3)
% 1.68/0.97      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
% 1.68/0.97      | ~ m1_pre_topc(X0,sK2)
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 1.68/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 1.68/0.97      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.97      | ~ r2_hidden(X3,u1_struct_0(sK4))
% 1.68/0.97      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 1.68/0.97      | ~ v1_funct_1(X2)
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X1) ),
% 1.68/0.97      inference(renaming,[status(thm)],[c_531]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_688,plain,
% 1.68/0.97      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,X2,X0),X3)
% 1.68/0.97      | r1_tmap_1(sK2,X1,X2,X3)
% 1.68/0.97      | ~ m1_pre_topc(X0,sK2)
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 1.68/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 1.68/0.97      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.97      | ~ r2_hidden(X3,u1_struct_0(sK4))
% 1.68/0.97      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 1.68/0.97      | ~ v1_funct_1(X2)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.68/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.68/0.97      | sK3 != X2 ),
% 1.68/0.97      inference(resolution_lifted,[status(thm)],[c_27,c_532]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_689,plain,
% 1.68/0.97      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
% 1.68/0.97      | r1_tmap_1(sK2,X1,sK3,X2)
% 1.68/0.97      | ~ m1_pre_topc(X0,sK2)
% 1.68/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.68/0.97      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 1.68/0.97      | ~ r2_hidden(X2,u1_struct_0(sK4))
% 1.68/0.97      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 1.68/0.97      | ~ v1_funct_1(sK3)
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.68/0.97      inference(unflattening,[status(thm)],[c_688]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_693,plain,
% 1.68/0.97      ( ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 1.68/0.97      | ~ r2_hidden(X2,u1_struct_0(sK4))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 1.68/0.97      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.97      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.68/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_pre_topc(X0,sK2)
% 1.68/0.97      | r1_tmap_1(sK2,X1,sK3,X2)
% 1.68/0.97      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.68/0.97      inference(global_propositional_subsumption,
% 1.68/0.97                [status(thm)],
% 1.68/0.97                [c_689,c_28]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_694,plain,
% 1.68/0.97      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
% 1.68/0.97      | r1_tmap_1(sK2,X1,sK3,X2)
% 1.68/0.97      | ~ m1_pre_topc(X0,sK2)
% 1.68/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.68/0.97      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 1.68/0.97      | ~ r2_hidden(X2,u1_struct_0(sK4))
% 1.68/0.97      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.68/0.97      inference(renaming,[status(thm)],[c_693]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_834,plain,
% 1.68/0.97      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
% 1.68/0.97      | r1_tmap_1(sK2,X1,sK3,X2)
% 1.68/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.68/0.97      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.68/0.97      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 1.68/0.97      | ~ r2_hidden(X2,u1_struct_0(sK4))
% 1.68/0.97      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.68/0.97      | sK2 != sK2
% 1.68/0.97      | sK4 != X0 ),
% 1.68/0.97      inference(resolution_lifted,[status(thm)],[c_23,c_694]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_835,plain,
% 1.68/0.97      ( r1_tmap_1(sK2,X0,sK3,X1)
% 1.68/0.97      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.68/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.68/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.68/0.97      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.68/0.97      | ~ r2_hidden(X1,u1_struct_0(sK4))
% 1.68/0.97      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | v2_struct_0(sK4)
% 1.68/0.97      | ~ l1_pre_topc(X0)
% 1.68/0.97      | ~ v2_pre_topc(X0)
% 1.68/0.97      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 1.68/0.97      inference(unflattening,[status(thm)],[c_834]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_744,plain,
% 1.68/0.97      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | sK2 != X1
% 1.68/0.97      | sK4 != X0 ),
% 1.68/0.97      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_745,plain,
% 1.68/0.97      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.97      | ~ l1_pre_topc(sK2) ),
% 1.68/0.97      inference(unflattening,[status(thm)],[c_744]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_839,plain,
% 1.68/0.97      ( v2_struct_0(X0)
% 1.68/0.97      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
% 1.68/0.97      | ~ r2_hidden(X1,u1_struct_0(sK4))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.68/0.97      | r1_tmap_1(sK2,X0,sK3,X1)
% 1.68/0.97      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.68/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.68/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.68/0.97      | ~ l1_pre_topc(X0)
% 1.68/0.97      | ~ v2_pre_topc(X0)
% 1.68/0.97      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 1.68/0.97      inference(global_propositional_subsumption,
% 1.68/0.97                [status(thm)],
% 1.68/0.97                [c_835,c_29,c_25,c_745]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_840,plain,
% 1.68/0.97      ( r1_tmap_1(sK2,X0,sK3,X1)
% 1.68/0.97      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.68/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.68/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.68/0.97      | ~ r2_hidden(X1,u1_struct_0(sK4))
% 1.68/0.97      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | ~ l1_pre_topc(X0)
% 1.68/0.97      | ~ v2_pre_topc(X0)
% 1.68/0.97      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 1.68/0.97      inference(renaming,[status(thm)],[c_839]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_755,plain,
% 1.68/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.68/0.97      | m1_subset_1(X0,u1_struct_0(X2))
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | v2_struct_0(X2)
% 1.68/0.97      | ~ l1_pre_topc(X2)
% 1.68/0.97      | sK2 != X2
% 1.68/0.97      | sK4 != X1 ),
% 1.68/0.97      inference(resolution_lifted,[status(thm)],[c_7,c_23]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_756,plain,
% 1.68/0.97      ( m1_subset_1(X0,u1_struct_0(sK2))
% 1.68/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.68/0.97      | v2_struct_0(sK2)
% 1.68/0.97      | v2_struct_0(sK4)
% 1.68/0.97      | ~ l1_pre_topc(sK2) ),
% 1.68/0.97      inference(unflattening,[status(thm)],[c_755]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_760,plain,
% 1.68/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.68/0.97      | m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.68/0.97      inference(global_propositional_subsumption,
% 1.68/0.97                [status(thm)],
% 1.68/0.97                [c_756,c_31,c_29,c_25]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_761,plain,
% 1.68/0.97      ( m1_subset_1(X0,u1_struct_0(sK2))
% 1.68/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 1.68/0.97      inference(renaming,[status(thm)],[c_760]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_856,plain,
% 1.68/0.97      ( r1_tmap_1(sK2,X0,sK3,X1)
% 1.68/0.97      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.68/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.68/0.97      | ~ r2_hidden(X1,u1_struct_0(sK4))
% 1.68/0.97      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | ~ l1_pre_topc(X0)
% 1.68/0.97      | ~ v2_pre_topc(X0)
% 1.68/0.97      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 1.68/0.97      inference(forward_subsumption_resolution,
% 1.68/0.97                [status(thm)],
% 1.68/0.97                [c_840,c_761]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_1,plain,
% 1.68/0.97      ( r1_tarski(X0,X0) ),
% 1.68/0.97      inference(cnf_transformation,[],[f90]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_867,plain,
% 1.68/0.97      ( r1_tmap_1(sK2,X0,sK3,X1)
% 1.68/0.97      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.68/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.68/0.97      | ~ r2_hidden(X1,u1_struct_0(sK4))
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | ~ l1_pre_topc(X0)
% 1.68/0.97      | ~ v2_pre_topc(X0)
% 1.68/0.97      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 1.68/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_856,c_1]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_1103,plain,
% 1.68/0.97      ( r1_tmap_1(sK2,X0,sK3,X1)
% 1.68/0.97      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.68/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.68/0.97      | ~ r2_hidden(X1,u1_struct_0(sK4))
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | ~ l1_pre_topc(X0)
% 1.68/0.97      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.68/0.97      | sK1 != X0 ),
% 1.68/0.97      inference(resolution_lifted,[status(thm)],[c_867,c_33]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_1104,plain,
% 1.68/0.97      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 1.68/0.97      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.68/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.68/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.68/0.97      | ~ r2_hidden(X0,u1_struct_0(sK4))
% 1.68/0.97      | v2_struct_0(sK1)
% 1.68/0.97      | ~ l1_pre_topc(sK1)
% 1.68/0.97      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.68/0.97      inference(unflattening,[status(thm)],[c_1103]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_1108,plain,
% 1.68/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.68/0.97      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.68/0.97      | r1_tmap_1(sK2,sK1,sK3,X0)
% 1.68/0.97      | ~ r2_hidden(X0,u1_struct_0(sK4))
% 1.68/0.97      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.68/0.97      inference(global_propositional_subsumption,
% 1.68/0.97                [status(thm)],
% 1.68/0.97                [c_1104,c_34,c_32,c_26]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_1109,plain,
% 1.68/0.97      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 1.68/0.97      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.68/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.68/0.97      | ~ r2_hidden(X0,u1_struct_0(sK4))
% 1.68/0.97      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.68/0.97      inference(renaming,[status(thm)],[c_1108]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_1841,plain,
% 1.68/0.97      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 1.68/0.97      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.68/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.68/0.97      | ~ r2_hidden(X0,u1_struct_0(sK4)) ),
% 1.68/0.97      inference(equality_resolution_simp,[status(thm)],[c_1109]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_3328,plain,
% 1.68/0.97      ( r1_tmap_1(sK2,sK1,sK3,sK6)
% 1.68/0.97      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 1.68/0.97      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 1.68/0.97      | ~ r2_hidden(sK6,u1_struct_0(sK4)) ),
% 1.68/0.97      inference(instantiation,[status(thm)],[c_1841]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_10,plain,
% 1.68/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 1.68/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.68/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.97      | r2_hidden(X2,X0)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X1) ),
% 1.68/0.97      inference(cnf_transformation,[],[f65]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_8,plain,
% 1.68/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 1.68/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.68/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X1) ),
% 1.68/0.97      inference(cnf_transformation,[],[f63]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_202,plain,
% 1.68/0.97      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.68/0.97      | ~ m1_connsp_2(X0,X1,X2)
% 1.68/0.97      | r2_hidden(X2,X0)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X1) ),
% 1.68/0.97      inference(global_propositional_subsumption,
% 1.68/0.97                [status(thm)],
% 1.68/0.97                [c_10,c_8]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_203,plain,
% 1.68/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 1.68/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.68/0.97      | r2_hidden(X2,X0)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X1) ),
% 1.68/0.97      inference(renaming,[status(thm)],[c_202]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_9,plain,
% 1.68/0.97      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 1.68/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.68/0.97      | v2_struct_0(X0)
% 1.68/0.97      | ~ l1_pre_topc(X0)
% 1.68/0.97      | ~ v2_pre_topc(X0) ),
% 1.68/0.97      inference(cnf_transformation,[],[f64]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_472,plain,
% 1.68/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.68/0.97      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 1.68/0.97      | r2_hidden(X0,X4)
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | v2_struct_0(X3)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ l1_pre_topc(X3)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X3)
% 1.68/0.97      | X3 != X1
% 1.68/0.97      | X2 != X0
% 1.68/0.97      | sK0(X3,X2) != X4 ),
% 1.68/0.97      inference(resolution_lifted,[status(thm)],[c_203,c_9]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_473,plain,
% 1.68/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.68/0.97      | r2_hidden(X0,sK0(X1,X0))
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X1) ),
% 1.68/0.97      inference(unflattening,[status(thm)],[c_472]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_5,plain,
% 1.68/0.97      ( ~ m1_pre_topc(X0,X1)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | v2_pre_topc(X0) ),
% 1.68/0.97      inference(cnf_transformation,[],[f60]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_784,plain,
% 1.68/0.97      ( ~ l1_pre_topc(X0)
% 1.68/0.97      | ~ v2_pre_topc(X0)
% 1.68/0.97      | v2_pre_topc(X1)
% 1.68/0.97      | sK2 != X0
% 1.68/0.97      | sK4 != X1 ),
% 1.68/0.97      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_785,plain,
% 1.68/0.97      ( ~ l1_pre_topc(sK2) | ~ v2_pre_topc(sK2) | v2_pre_topc(sK4) ),
% 1.68/0.97      inference(unflattening,[status(thm)],[c_784]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_787,plain,
% 1.68/0.97      ( v2_pre_topc(sK4) ),
% 1.68/0.97      inference(global_propositional_subsumption,
% 1.68/0.97                [status(thm)],
% 1.68/0.97                [c_785,c_30,c_29]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_1301,plain,
% 1.68/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.68/0.97      | r2_hidden(X0,sK0(X1,X0))
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | sK4 != X1 ),
% 1.68/0.97      inference(resolution_lifted,[status(thm)],[c_473,c_787]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_1302,plain,
% 1.68/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.68/0.97      | r2_hidden(X0,sK0(sK4,X0))
% 1.68/0.97      | v2_struct_0(sK4)
% 1.68/0.97      | ~ l1_pre_topc(sK4) ),
% 1.68/0.97      inference(unflattening,[status(thm)],[c_1301]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_6,plain,
% 1.68/0.97      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.68/0.97      inference(cnf_transformation,[],[f61]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_773,plain,
% 1.68/0.97      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X0 | sK4 != X1 ),
% 1.68/0.97      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_774,plain,
% 1.68/0.97      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK4) ),
% 1.68/0.97      inference(unflattening,[status(thm)],[c_773]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_1306,plain,
% 1.68/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK4)) | r2_hidden(X0,sK0(sK4,X0)) ),
% 1.68/0.97      inference(global_propositional_subsumption,
% 1.68/0.97                [status(thm)],
% 1.68/0.97                [c_1302,c_29,c_25,c_774]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_3318,plain,
% 1.68/0.97      ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 1.68/0.97      | r2_hidden(sK6,sK0(sK4,sK6)) ),
% 1.68/0.97      inference(instantiation,[status(thm)],[c_1306]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_493,plain,
% 1.68/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.68/0.97      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 1.68/0.97      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | v2_struct_0(X3)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ l1_pre_topc(X3)
% 1.68/0.97      | ~ v2_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X3)
% 1.68/0.97      | X3 != X1
% 1.68/0.97      | X2 != X0
% 1.68/0.97      | sK0(X3,X2) != X4 ),
% 1.68/0.97      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_494,plain,
% 1.68/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.68/0.97      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | ~ v2_pre_topc(X1) ),
% 1.68/0.97      inference(unflattening,[status(thm)],[c_493]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_1283,plain,
% 1.68/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.68/0.97      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.97      | v2_struct_0(X1)
% 1.68/0.97      | ~ l1_pre_topc(X1)
% 1.68/0.97      | sK4 != X1 ),
% 1.68/0.97      inference(resolution_lifted,[status(thm)],[c_494,c_787]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_1284,plain,
% 1.68/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.68/0.97      | m1_subset_1(sK0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.68/0.97      | v2_struct_0(sK4)
% 1.68/0.97      | ~ l1_pre_topc(sK4) ),
% 1.68/0.97      inference(unflattening,[status(thm)],[c_1283]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_1288,plain,
% 1.68/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.68/0.97      | m1_subset_1(sK0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.68/0.97      inference(global_propositional_subsumption,
% 1.68/0.97                [status(thm)],
% 1.68/0.97                [c_1284,c_29,c_25,c_774]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_3315,plain,
% 1.68/0.97      ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.68/0.97      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.68/0.97      inference(instantiation,[status(thm)],[c_1288]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_19,negated_conjecture,
% 1.68/0.97      ( r1_tmap_1(sK2,sK1,sK3,sK5)
% 1.68/0.97      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 1.68/0.97      inference(cnf_transformation,[],[f88]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_3097,plain,
% 1.68/0.97      ( r1_tmap_1(sK2,sK1,sK3,sK5) = iProver_top
% 1.68/0.97      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
% 1.68/0.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_3156,plain,
% 1.68/0.97      ( r1_tmap_1(sK2,sK1,sK3,sK6) = iProver_top
% 1.68/0.97      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
% 1.68/0.97      inference(light_normalisation,[status(thm)],[c_3097,c_20]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(c_3251,plain,
% 1.68/0.97      ( r1_tmap_1(sK2,sK1,sK3,sK6)
% 1.68/0.97      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 1.68/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_3156]) ).
% 1.68/0.97  
% 1.68/0.97  cnf(contradiction,plain,
% 1.68/0.97      ( $false ),
% 1.68/0.97      inference(minisat,
% 1.68/0.97                [status(thm)],
% 1.68/0.97                [c_3840,c_3348,c_3331,c_3328,c_3318,c_3315,c_3251,c_21]) ).
% 1.68/0.97  
% 1.68/0.97  
% 1.68/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 1.68/0.97  
% 1.68/0.97  ------                               Statistics
% 1.68/0.97  
% 1.68/0.97  ------ General
% 1.68/0.97  
% 1.68/0.97  abstr_ref_over_cycles:                  0
% 1.68/0.97  abstr_ref_under_cycles:                 0
% 1.68/0.97  gc_basic_clause_elim:                   0
% 1.68/0.97  forced_gc_time:                         0
% 1.68/0.97  parsing_time:                           0.009
% 1.68/0.97  unif_index_cands_time:                  0.
% 1.68/0.97  unif_index_add_time:                    0.
% 1.68/0.97  orderings_time:                         0.
% 1.68/0.97  out_proof_time:                         0.02
% 1.68/0.97  total_time:                             0.121
% 1.68/0.97  num_of_symbols:                         60
% 1.68/0.97  num_of_terms:                           1914
% 1.68/0.97  
% 1.68/0.97  ------ Preprocessing
% 1.68/0.97  
% 1.68/0.97  num_of_splits:                          4
% 1.68/0.97  num_of_split_atoms:                     4
% 1.68/0.97  num_of_reused_defs:                     0
% 1.68/0.97  num_eq_ax_congr_red:                    19
% 1.68/0.97  num_of_sem_filtered_clauses:            1
% 1.68/0.97  num_of_subtypes:                        0
% 1.68/0.97  monotx_restored_types:                  0
% 1.68/0.97  sat_num_of_epr_types:                   0
% 1.68/0.97  sat_num_of_non_cyclic_types:            0
% 1.68/0.97  sat_guarded_non_collapsed_types:        0
% 1.68/0.97  num_pure_diseq_elim:                    0
% 1.68/0.97  simp_replaced_by:                       0
% 1.68/0.97  res_preprocessed:                       134
% 1.68/0.97  prep_upred:                             0
% 1.68/0.97  prep_unflattend:                        89
% 1.68/0.97  smt_new_axioms:                         0
% 1.68/0.97  pred_elim_cands:                        5
% 1.68/0.97  pred_elim:                              9
% 1.68/0.97  pred_elim_cl:                           9
% 1.68/0.97  pred_elim_cycles:                       14
% 1.68/0.97  merged_defs:                            8
% 1.68/0.97  merged_defs_ncl:                        0
% 1.68/0.97  bin_hyper_res:                          8
% 1.68/0.97  prep_cycles:                            4
% 1.68/0.97  pred_elim_time:                         0.031
% 1.68/0.97  splitting_time:                         0.
% 1.68/0.97  sem_filter_time:                        0.
% 1.68/0.97  monotx_time:                            0.
% 1.68/0.97  subtype_inf_time:                       0.
% 1.68/0.97  
% 1.68/0.97  ------ Problem properties
% 1.68/0.97  
% 1.68/0.97  clauses:                                28
% 1.68/0.97  conjectures:                            6
% 1.68/0.97  epr:                                    4
% 1.68/0.97  horn:                                   26
% 1.68/0.97  ground:                                 11
% 1.68/0.97  unary:                                  6
% 1.68/0.97  binary:                                 9
% 1.68/0.97  lits:                                   70
% 1.68/0.97  lits_eq:                                6
% 1.68/0.97  fd_pure:                                0
% 1.68/0.97  fd_pseudo:                              0
% 1.68/0.97  fd_cond:                                0
% 1.68/0.97  fd_pseudo_cond:                         1
% 1.68/0.97  ac_symbols:                             0
% 1.68/0.97  
% 1.68/0.97  ------ Propositional Solver
% 1.68/0.97  
% 1.68/0.97  prop_solver_calls:                      25
% 1.68/0.97  prop_fast_solver_calls:                 1395
% 1.68/0.97  smt_solver_calls:                       0
% 1.68/0.97  smt_fast_solver_calls:                  0
% 1.68/0.97  prop_num_of_clauses:                    745
% 1.68/0.97  prop_preprocess_simplified:             4067
% 1.68/0.97  prop_fo_subsumed:                       64
% 1.68/0.97  prop_solver_time:                       0.
% 1.68/0.97  smt_solver_time:                        0.
% 1.68/0.97  smt_fast_solver_time:                   0.
% 1.68/0.97  prop_fast_solver_time:                  0.
% 1.68/0.97  prop_unsat_core_time:                   0.
% 1.68/0.97  
% 1.68/0.97  ------ QBF
% 1.68/0.97  
% 1.68/0.97  qbf_q_res:                              0
% 1.68/0.97  qbf_num_tautologies:                    0
% 1.68/0.97  qbf_prep_cycles:                        0
% 1.68/0.97  
% 1.68/0.97  ------ BMC1
% 1.68/0.97  
% 1.68/0.97  bmc1_current_bound:                     -1
% 1.68/0.97  bmc1_last_solved_bound:                 -1
% 1.68/0.97  bmc1_unsat_core_size:                   -1
% 1.68/0.97  bmc1_unsat_core_parents_size:           -1
% 1.68/0.97  bmc1_merge_next_fun:                    0
% 1.68/0.97  bmc1_unsat_core_clauses_time:           0.
% 1.68/0.97  
% 1.68/0.97  ------ Instantiation
% 1.68/0.97  
% 1.68/0.97  inst_num_of_clauses:                    150
% 1.68/0.97  inst_num_in_passive:                    52
% 1.68/0.97  inst_num_in_active:                     84
% 1.68/0.97  inst_num_in_unprocessed:                13
% 1.68/0.97  inst_num_of_loops:                      87
% 1.68/0.97  inst_num_of_learning_restarts:          0
% 1.68/0.97  inst_num_moves_active_passive:          0
% 1.68/0.97  inst_lit_activity:                      0
% 1.68/0.97  inst_lit_activity_moves:                0
% 1.68/0.97  inst_num_tautologies:                   0
% 1.68/0.97  inst_num_prop_implied:                  0
% 1.68/0.97  inst_num_existing_simplified:           0
% 1.68/0.97  inst_num_eq_res_simplified:             0
% 1.68/0.97  inst_num_child_elim:                    0
% 1.68/0.97  inst_num_of_dismatching_blockings:      0
% 1.68/0.97  inst_num_of_non_proper_insts:           94
% 1.68/0.97  inst_num_of_duplicates:                 0
% 1.68/0.97  inst_inst_num_from_inst_to_res:         0
% 1.68/0.97  inst_dismatching_checking_time:         0.
% 1.68/0.97  
% 1.68/0.97  ------ Resolution
% 1.68/0.97  
% 1.68/0.97  res_num_of_clauses:                     0
% 1.68/0.97  res_num_in_passive:                     0
% 1.68/0.97  res_num_in_active:                      0
% 1.68/0.97  res_num_of_loops:                       138
% 1.68/0.97  res_forward_subset_subsumed:            5
% 1.68/0.97  res_backward_subset_subsumed:           0
% 1.68/0.97  res_forward_subsumed:                   0
% 1.68/0.97  res_backward_subsumed:                  0
% 1.68/0.97  res_forward_subsumption_resolution:     3
% 1.68/0.97  res_backward_subsumption_resolution:    0
% 1.68/0.97  res_clause_to_clause_subsumption:       85
% 1.68/0.97  res_orphan_elimination:                 0
% 1.68/0.97  res_tautology_del:                      24
% 1.68/0.97  res_num_eq_res_simplified:              2
% 1.68/0.97  res_num_sel_changes:                    0
% 1.68/0.97  res_moves_from_active_to_pass:          0
% 1.68/0.97  
% 1.68/0.97  ------ Superposition
% 1.68/0.97  
% 1.68/0.97  sup_time_total:                         0.
% 1.68/0.97  sup_time_generating:                    0.
% 1.68/0.97  sup_time_sim_full:                      0.
% 1.68/0.97  sup_time_sim_immed:                     0.
% 1.68/0.97  
% 1.68/0.97  sup_num_of_clauses:                     36
% 1.68/0.97  sup_num_in_active:                      16
% 1.68/0.97  sup_num_in_passive:                     20
% 1.68/0.97  sup_num_of_loops:                       16
% 1.68/0.97  sup_fw_superposition:                   9
% 1.68/0.97  sup_bw_superposition:                   0
% 1.68/0.97  sup_immediate_simplified:               0
% 1.68/0.97  sup_given_eliminated:                   0
% 1.68/0.97  comparisons_done:                       0
% 1.68/0.97  comparisons_avoided:                    0
% 1.68/0.97  
% 1.68/0.97  ------ Simplifications
% 1.68/0.97  
% 1.68/0.97  
% 1.68/0.97  sim_fw_subset_subsumed:                 0
% 1.68/0.97  sim_bw_subset_subsumed:                 0
% 1.68/0.97  sim_fw_subsumed:                        0
% 1.68/0.97  sim_bw_subsumed:                        0
% 1.68/0.97  sim_fw_subsumption_res:                 0
% 1.68/0.97  sim_bw_subsumption_res:                 0
% 1.68/0.97  sim_tautology_del:                      0
% 1.68/0.97  sim_eq_tautology_del:                   0
% 1.68/0.97  sim_eq_res_simp:                        0
% 1.68/0.97  sim_fw_demodulated:                     0
% 1.68/0.97  sim_bw_demodulated:                     0
% 1.68/0.97  sim_light_normalised:                   3
% 1.68/0.97  sim_joinable_taut:                      0
% 1.68/0.97  sim_joinable_simp:                      0
% 1.68/0.97  sim_ac_normalised:                      0
% 1.68/0.97  sim_smt_subsumption:                    0
% 1.68/0.97  
%------------------------------------------------------------------------------
