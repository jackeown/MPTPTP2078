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
% DateTime   : Thu Dec  3 12:22:45 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 756 expanded)
%              Number of clauses        :  105 ( 133 expanded)
%              Number of leaves         :   19 ( 304 expanded)
%              Depth                    :   35
%              Number of atoms          : 1315 (12142 expanded)
%              Number of equality atoms :  152 ( 925 expanded)
%              Maximal formula depth    :   28 (   8 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(negated_conjecture,[],[f10])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f33,f39,f38,f37,f36,f35,f34])).

fof(f66,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
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
    inference(equality_resolution,[],[f53])).

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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
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
    inference(equality_resolution,[],[f52])).

fof(f62,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
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
    inference(equality_resolution,[],[f54])).

fof(f6,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f67,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1331,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2253,plain,
    ( k2_tmap_1(sK1,sK0,sK2,sK3) = k2_tmap_1(sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1331])).

cnf(c_1337,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X5,X6,X7)
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | X7 != X3 ),
    theory(equality)).

cnf(c_1850,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | X2 != k2_tmap_1(sK1,sK0,sK2,sK3)
    | X3 != sK5
    | X1 != sK0
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1337])).

cnf(c_1905,plain,
    ( r1_tmap_1(X0,X1,X2,sK4)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | X2 != k2_tmap_1(sK1,sK0,sK2,sK3)
    | X1 != sK0
    | X0 != sK3
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_1850])).

cnf(c_1951,plain,
    ( r1_tmap_1(X0,sK0,X1,sK4)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | X1 != k2_tmap_1(sK1,sK0,sK2,sK3)
    | X0 != sK3
    | sK4 != sK5
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1905])).

cnf(c_2119,plain,
    ( r1_tmap_1(sK3,sK0,X0,sK4)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | X0 != k2_tmap_1(sK1,sK0,sK2,sK3)
    | sK4 != sK5
    | sK0 != sK0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1951])).

cnf(c_2252,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | k2_tmap_1(sK1,sK0,sK2,sK3) != k2_tmap_1(sK1,sK0,sK2,sK3)
    | sK4 != sK5
    | sK0 != sK0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2119])).

cnf(c_2120,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1331])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_13,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X5,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X5)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f77])).

cnf(c_160,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_11])).

cnf(c_161,plain,
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
    inference(renaming,[status(thm)],[c_160])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_609,plain,
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
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_161,c_23])).

cnf(c_610,plain,
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
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_614,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_610,c_24])).

cnf(c_615,plain,
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
    inference(renaming,[status(thm)],[c_614])).

cnf(c_855,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
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
    inference(resolution_lifted,[status(thm)],[c_19,c_615])).

cnf(c_856,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
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
    inference(unflattening,[status(thm)],[c_855])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_860,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_856,c_27,c_26,c_25,c_21])).

cnf(c_861,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_860])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1104,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_861,c_29])).

cnf(c_1105,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_1104])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1109,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ r1_tmap_1(sK1,sK0,sK2,X0)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1105,c_30,c_28,c_22])).

cnf(c_1110,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_1109])).

cnf(c_1223,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1110])).

cnf(c_1690,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1223])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1701,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16,negated_conjecture,
    ( sK4 = sK5 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1728,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1701,c_16])).

cnf(c_2003,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1690,c_1728])).

cnf(c_2004,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2003])).

cnf(c_1952,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1331])).

cnf(c_1936,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1331])).

cnf(c_1333,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1826,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | X1 != u1_struct_0(sK3)
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_1333])).

cnf(c_1865,plain,
    ( m1_subset_1(sK4,X0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | X0 != u1_struct_0(sK3)
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_1826])).

cnf(c_1935,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_1865])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_6,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_385,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_4,c_6])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_844,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_19])).

cnf(c_845,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_844])).

cnf(c_847,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_845,c_25])).

cnf(c_1181,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_385,c_847])).

cnf(c_1182,plain,
    ( v2_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1181])).

cnf(c_1184,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1182,c_21])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_12,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X5,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X5)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_9,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_168,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_10])).

cnf(c_169,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_168])).

cnf(c_20,negated_conjecture,
    ( v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_426,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_169,c_20])).

cnf(c_427,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_429,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_427,c_26,c_25,c_19])).

cnf(c_439,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X5)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK3) != X5
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_429])).

cnf(c_440,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X3,u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_444,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ r2_hidden(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,sK1)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_27,c_26,c_25])).

cnf(c_445,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X3,u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_444])).

cnf(c_495,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X5)
    | X3 != X4
    | u1_struct_0(sK3) != X5 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_445])).

cnf(c_496,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_718,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_496])).

cnf(c_719,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
    | r1_tmap_1(sK1,X1,sK2,X2)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v1_funct_1(sK2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_718])).

cnf(c_723,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | r1_tmap_1(sK1,X1,sK2,X2)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_719,c_24])).

cnf(c_724,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
    | r1_tmap_1(sK1,X1,sK2,X2)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_723])).

cnf(c_897,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
    | r1_tmap_1(sK1,X1,sK2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK1 != sK1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_724])).

cnf(c_898,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_897])).

cnf(c_833,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_834,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_833])).

cnf(c_902,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_898,c_25,c_21,c_834])).

cnf(c_903,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_902])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_930,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_903,c_1])).

cnf(c_1074,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_930,c_29])).

cnf(c_1075,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_1074])).

cnf(c_1079,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | r1_tmap_1(sK1,sK0,sK2,X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1075,c_30,c_28,c_22])).

cnf(c_1080,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_1079])).

cnf(c_1198,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1184,c_1080])).

cnf(c_1218,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1198])).

cnf(c_1817,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1698,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1708,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1698,c_16])).

cnf(c_1785,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1708])).

cnf(c_15,negated_conjecture,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1700,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1723,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1700,c_16])).

cnf(c_1781,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1723])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2253,c_2252,c_2120,c_2004,c_1952,c_1936,c_1935,c_1817,c_1785,c_1781,c_14,c_16,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n025.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 10:43:05 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.72/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.02  
% 1.72/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.72/1.02  
% 1.72/1.02  ------  iProver source info
% 1.72/1.02  
% 1.72/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.72/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.72/1.02  git: non_committed_changes: false
% 1.72/1.02  git: last_make_outside_of_git: false
% 1.72/1.02  
% 1.72/1.02  ------ 
% 1.72/1.02  
% 1.72/1.02  ------ Input Options
% 1.72/1.02  
% 1.72/1.02  --out_options                           all
% 1.72/1.02  --tptp_safe_out                         true
% 1.72/1.02  --problem_path                          ""
% 1.72/1.02  --include_path                          ""
% 1.72/1.02  --clausifier                            res/vclausify_rel
% 1.72/1.02  --clausifier_options                    --mode clausify
% 1.72/1.02  --stdin                                 false
% 1.72/1.02  --stats_out                             all
% 1.72/1.02  
% 1.72/1.02  ------ General Options
% 1.72/1.02  
% 1.72/1.02  --fof                                   false
% 1.72/1.02  --time_out_real                         305.
% 1.72/1.02  --time_out_virtual                      -1.
% 1.72/1.02  --symbol_type_check                     false
% 1.72/1.02  --clausify_out                          false
% 1.72/1.02  --sig_cnt_out                           false
% 1.72/1.02  --trig_cnt_out                          false
% 1.72/1.02  --trig_cnt_out_tolerance                1.
% 1.72/1.02  --trig_cnt_out_sk_spl                   false
% 1.72/1.02  --abstr_cl_out                          false
% 1.72/1.02  
% 1.72/1.02  ------ Global Options
% 1.72/1.02  
% 1.72/1.02  --schedule                              default
% 1.72/1.02  --add_important_lit                     false
% 1.72/1.02  --prop_solver_per_cl                    1000
% 1.72/1.02  --min_unsat_core                        false
% 1.72/1.02  --soft_assumptions                      false
% 1.72/1.02  --soft_lemma_size                       3
% 1.72/1.02  --prop_impl_unit_size                   0
% 1.72/1.02  --prop_impl_unit                        []
% 1.72/1.02  --share_sel_clauses                     true
% 1.72/1.02  --reset_solvers                         false
% 1.72/1.02  --bc_imp_inh                            [conj_cone]
% 1.72/1.02  --conj_cone_tolerance                   3.
% 1.72/1.02  --extra_neg_conj                        none
% 1.72/1.02  --large_theory_mode                     true
% 1.72/1.02  --prolific_symb_bound                   200
% 1.72/1.02  --lt_threshold                          2000
% 1.72/1.02  --clause_weak_htbl                      true
% 1.72/1.02  --gc_record_bc_elim                     false
% 1.72/1.02  
% 1.72/1.02  ------ Preprocessing Options
% 1.72/1.02  
% 1.72/1.02  --preprocessing_flag                    true
% 1.72/1.02  --time_out_prep_mult                    0.1
% 1.72/1.02  --splitting_mode                        input
% 1.72/1.02  --splitting_grd                         true
% 1.72/1.02  --splitting_cvd                         false
% 1.72/1.02  --splitting_cvd_svl                     false
% 1.72/1.02  --splitting_nvd                         32
% 1.72/1.02  --sub_typing                            true
% 1.72/1.02  --prep_gs_sim                           true
% 1.72/1.02  --prep_unflatten                        true
% 1.72/1.02  --prep_res_sim                          true
% 1.72/1.02  --prep_upred                            true
% 1.72/1.02  --prep_sem_filter                       exhaustive
% 1.72/1.02  --prep_sem_filter_out                   false
% 1.72/1.02  --pred_elim                             true
% 1.72/1.02  --res_sim_input                         true
% 1.72/1.02  --eq_ax_congr_red                       true
% 1.72/1.02  --pure_diseq_elim                       true
% 1.72/1.02  --brand_transform                       false
% 1.72/1.02  --non_eq_to_eq                          false
% 1.72/1.02  --prep_def_merge                        true
% 1.72/1.02  --prep_def_merge_prop_impl              false
% 1.72/1.02  --prep_def_merge_mbd                    true
% 1.72/1.02  --prep_def_merge_tr_red                 false
% 1.72/1.02  --prep_def_merge_tr_cl                  false
% 1.72/1.02  --smt_preprocessing                     true
% 1.72/1.02  --smt_ac_axioms                         fast
% 1.72/1.02  --preprocessed_out                      false
% 1.72/1.02  --preprocessed_stats                    false
% 1.72/1.02  
% 1.72/1.02  ------ Abstraction refinement Options
% 1.72/1.02  
% 1.72/1.02  --abstr_ref                             []
% 1.72/1.02  --abstr_ref_prep                        false
% 1.72/1.02  --abstr_ref_until_sat                   false
% 1.72/1.02  --abstr_ref_sig_restrict                funpre
% 1.72/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.72/1.02  --abstr_ref_under                       []
% 1.72/1.02  
% 1.72/1.02  ------ SAT Options
% 1.72/1.02  
% 1.72/1.02  --sat_mode                              false
% 1.72/1.02  --sat_fm_restart_options                ""
% 1.72/1.02  --sat_gr_def                            false
% 1.72/1.02  --sat_epr_types                         true
% 1.72/1.02  --sat_non_cyclic_types                  false
% 1.72/1.02  --sat_finite_models                     false
% 1.72/1.02  --sat_fm_lemmas                         false
% 1.72/1.02  --sat_fm_prep                           false
% 1.72/1.02  --sat_fm_uc_incr                        true
% 1.72/1.02  --sat_out_model                         small
% 1.72/1.02  --sat_out_clauses                       false
% 1.72/1.02  
% 1.72/1.02  ------ QBF Options
% 1.72/1.02  
% 1.72/1.02  --qbf_mode                              false
% 1.72/1.02  --qbf_elim_univ                         false
% 1.72/1.02  --qbf_dom_inst                          none
% 1.72/1.02  --qbf_dom_pre_inst                      false
% 1.72/1.02  --qbf_sk_in                             false
% 1.72/1.02  --qbf_pred_elim                         true
% 1.72/1.02  --qbf_split                             512
% 1.72/1.02  
% 1.72/1.02  ------ BMC1 Options
% 1.72/1.02  
% 1.72/1.02  --bmc1_incremental                      false
% 1.72/1.02  --bmc1_axioms                           reachable_all
% 1.72/1.02  --bmc1_min_bound                        0
% 1.72/1.02  --bmc1_max_bound                        -1
% 1.72/1.02  --bmc1_max_bound_default                -1
% 1.72/1.02  --bmc1_symbol_reachability              true
% 1.72/1.02  --bmc1_property_lemmas                  false
% 1.72/1.02  --bmc1_k_induction                      false
% 1.72/1.02  --bmc1_non_equiv_states                 false
% 1.72/1.02  --bmc1_deadlock                         false
% 1.72/1.02  --bmc1_ucm                              false
% 1.72/1.02  --bmc1_add_unsat_core                   none
% 1.72/1.02  --bmc1_unsat_core_children              false
% 1.72/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.72/1.02  --bmc1_out_stat                         full
% 1.72/1.02  --bmc1_ground_init                      false
% 1.72/1.02  --bmc1_pre_inst_next_state              false
% 1.72/1.02  --bmc1_pre_inst_state                   false
% 1.72/1.02  --bmc1_pre_inst_reach_state             false
% 1.72/1.02  --bmc1_out_unsat_core                   false
% 1.72/1.02  --bmc1_aig_witness_out                  false
% 1.72/1.02  --bmc1_verbose                          false
% 1.72/1.02  --bmc1_dump_clauses_tptp                false
% 1.72/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.72/1.02  --bmc1_dump_file                        -
% 1.72/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.72/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.72/1.02  --bmc1_ucm_extend_mode                  1
% 1.72/1.02  --bmc1_ucm_init_mode                    2
% 1.72/1.02  --bmc1_ucm_cone_mode                    none
% 1.72/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.72/1.02  --bmc1_ucm_relax_model                  4
% 1.72/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.72/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.72/1.02  --bmc1_ucm_layered_model                none
% 1.72/1.02  --bmc1_ucm_max_lemma_size               10
% 1.72/1.02  
% 1.72/1.02  ------ AIG Options
% 1.72/1.02  
% 1.72/1.02  --aig_mode                              false
% 1.72/1.02  
% 1.72/1.02  ------ Instantiation Options
% 1.72/1.02  
% 1.72/1.02  --instantiation_flag                    true
% 1.72/1.02  --inst_sos_flag                         false
% 1.72/1.02  --inst_sos_phase                        true
% 1.72/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.72/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.72/1.02  --inst_lit_sel_side                     num_symb
% 1.72/1.02  --inst_solver_per_active                1400
% 1.72/1.02  --inst_solver_calls_frac                1.
% 1.72/1.02  --inst_passive_queue_type               priority_queues
% 1.72/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.72/1.02  --inst_passive_queues_freq              [25;2]
% 1.72/1.02  --inst_dismatching                      true
% 1.72/1.02  --inst_eager_unprocessed_to_passive     true
% 1.72/1.02  --inst_prop_sim_given                   true
% 1.72/1.02  --inst_prop_sim_new                     false
% 1.72/1.02  --inst_subs_new                         false
% 1.72/1.02  --inst_eq_res_simp                      false
% 1.72/1.02  --inst_subs_given                       false
% 1.72/1.02  --inst_orphan_elimination               true
% 1.72/1.02  --inst_learning_loop_flag               true
% 1.72/1.02  --inst_learning_start                   3000
% 1.72/1.02  --inst_learning_factor                  2
% 1.72/1.02  --inst_start_prop_sim_after_learn       3
% 1.72/1.02  --inst_sel_renew                        solver
% 1.72/1.02  --inst_lit_activity_flag                true
% 1.72/1.02  --inst_restr_to_given                   false
% 1.72/1.02  --inst_activity_threshold               500
% 1.72/1.02  --inst_out_proof                        true
% 1.72/1.02  
% 1.72/1.02  ------ Resolution Options
% 1.72/1.02  
% 1.72/1.02  --resolution_flag                       true
% 1.72/1.02  --res_lit_sel                           adaptive
% 1.72/1.02  --res_lit_sel_side                      none
% 1.72/1.02  --res_ordering                          kbo
% 1.72/1.02  --res_to_prop_solver                    active
% 1.72/1.02  --res_prop_simpl_new                    false
% 1.72/1.02  --res_prop_simpl_given                  true
% 1.72/1.02  --res_passive_queue_type                priority_queues
% 1.72/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.72/1.02  --res_passive_queues_freq               [15;5]
% 1.72/1.02  --res_forward_subs                      full
% 1.72/1.02  --res_backward_subs                     full
% 1.72/1.02  --res_forward_subs_resolution           true
% 1.72/1.02  --res_backward_subs_resolution          true
% 1.72/1.02  --res_orphan_elimination                true
% 1.72/1.02  --res_time_limit                        2.
% 1.72/1.02  --res_out_proof                         true
% 1.72/1.02  
% 1.72/1.02  ------ Superposition Options
% 1.72/1.02  
% 1.72/1.02  --superposition_flag                    true
% 1.72/1.02  --sup_passive_queue_type                priority_queues
% 1.72/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.72/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.72/1.02  --demod_completeness_check              fast
% 1.72/1.02  --demod_use_ground                      true
% 1.72/1.02  --sup_to_prop_solver                    passive
% 1.72/1.02  --sup_prop_simpl_new                    true
% 1.72/1.02  --sup_prop_simpl_given                  true
% 1.72/1.02  --sup_fun_splitting                     false
% 1.72/1.02  --sup_smt_interval                      50000
% 1.72/1.02  
% 1.72/1.02  ------ Superposition Simplification Setup
% 1.72/1.02  
% 1.72/1.02  --sup_indices_passive                   []
% 1.72/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.72/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.02  --sup_full_bw                           [BwDemod]
% 1.72/1.02  --sup_immed_triv                        [TrivRules]
% 1.72/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.72/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.02  --sup_immed_bw_main                     []
% 1.72/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.72/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/1.02  
% 1.72/1.02  ------ Combination Options
% 1.72/1.02  
% 1.72/1.02  --comb_res_mult                         3
% 1.72/1.02  --comb_sup_mult                         2
% 1.72/1.02  --comb_inst_mult                        10
% 1.72/1.02  
% 1.72/1.02  ------ Debug Options
% 1.72/1.02  
% 1.72/1.02  --dbg_backtrace                         false
% 1.72/1.02  --dbg_dump_prop_clauses                 false
% 1.72/1.02  --dbg_dump_prop_clauses_file            -
% 1.72/1.02  --dbg_out_stat                          false
% 1.72/1.02  ------ Parsing...
% 1.72/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.72/1.02  
% 1.72/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 1.72/1.02  
% 1.72/1.02  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.72/1.02  
% 1.72/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.72/1.02  ------ Proving...
% 1.72/1.02  ------ Problem Properties 
% 1.72/1.02  
% 1.72/1.02  
% 1.72/1.02  clauses                                 15
% 1.72/1.02  conjectures                             6
% 1.72/1.02  EPR                                     3
% 1.72/1.02  Horn                                    14
% 1.72/1.02  unary                                   6
% 1.72/1.02  binary                                  2
% 1.72/1.02  lits                                    37
% 1.72/1.02  lits eq                                 4
% 1.72/1.02  fd_pure                                 0
% 1.72/1.02  fd_pseudo                               0
% 1.72/1.02  fd_cond                                 0
% 1.72/1.02  fd_pseudo_cond                          1
% 1.72/1.02  AC symbols                              0
% 1.72/1.02  
% 1.72/1.02  ------ Schedule dynamic 5 is on 
% 1.72/1.02  
% 1.72/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.72/1.02  
% 1.72/1.02  
% 1.72/1.02  ------ 
% 1.72/1.02  Current options:
% 1.72/1.02  ------ 
% 1.72/1.02  
% 1.72/1.02  ------ Input Options
% 1.72/1.02  
% 1.72/1.02  --out_options                           all
% 1.72/1.02  --tptp_safe_out                         true
% 1.72/1.02  --problem_path                          ""
% 1.72/1.02  --include_path                          ""
% 1.72/1.02  --clausifier                            res/vclausify_rel
% 1.72/1.02  --clausifier_options                    --mode clausify
% 1.72/1.02  --stdin                                 false
% 1.72/1.02  --stats_out                             all
% 1.72/1.02  
% 1.72/1.02  ------ General Options
% 1.72/1.02  
% 1.72/1.02  --fof                                   false
% 1.72/1.02  --time_out_real                         305.
% 1.72/1.02  --time_out_virtual                      -1.
% 1.72/1.02  --symbol_type_check                     false
% 1.72/1.02  --clausify_out                          false
% 1.72/1.02  --sig_cnt_out                           false
% 1.72/1.02  --trig_cnt_out                          false
% 1.72/1.02  --trig_cnt_out_tolerance                1.
% 1.72/1.02  --trig_cnt_out_sk_spl                   false
% 1.72/1.02  --abstr_cl_out                          false
% 1.72/1.02  
% 1.72/1.02  ------ Global Options
% 1.72/1.02  
% 1.72/1.02  --schedule                              default
% 1.72/1.02  --add_important_lit                     false
% 1.72/1.02  --prop_solver_per_cl                    1000
% 1.72/1.02  --min_unsat_core                        false
% 1.72/1.02  --soft_assumptions                      false
% 1.72/1.02  --soft_lemma_size                       3
% 1.72/1.02  --prop_impl_unit_size                   0
% 1.72/1.02  --prop_impl_unit                        []
% 1.72/1.02  --share_sel_clauses                     true
% 1.72/1.02  --reset_solvers                         false
% 1.72/1.02  --bc_imp_inh                            [conj_cone]
% 1.72/1.02  --conj_cone_tolerance                   3.
% 1.72/1.02  --extra_neg_conj                        none
% 1.72/1.02  --large_theory_mode                     true
% 1.72/1.02  --prolific_symb_bound                   200
% 1.72/1.02  --lt_threshold                          2000
% 1.72/1.02  --clause_weak_htbl                      true
% 1.72/1.02  --gc_record_bc_elim                     false
% 1.72/1.02  
% 1.72/1.02  ------ Preprocessing Options
% 1.72/1.02  
% 1.72/1.02  --preprocessing_flag                    true
% 1.72/1.02  --time_out_prep_mult                    0.1
% 1.72/1.02  --splitting_mode                        input
% 1.72/1.02  --splitting_grd                         true
% 1.72/1.02  --splitting_cvd                         false
% 1.72/1.02  --splitting_cvd_svl                     false
% 1.72/1.02  --splitting_nvd                         32
% 1.72/1.02  --sub_typing                            true
% 1.72/1.02  --prep_gs_sim                           true
% 1.72/1.02  --prep_unflatten                        true
% 1.72/1.02  --prep_res_sim                          true
% 1.72/1.02  --prep_upred                            true
% 1.72/1.02  --prep_sem_filter                       exhaustive
% 1.72/1.02  --prep_sem_filter_out                   false
% 1.72/1.02  --pred_elim                             true
% 1.72/1.02  --res_sim_input                         true
% 1.72/1.02  --eq_ax_congr_red                       true
% 1.72/1.02  --pure_diseq_elim                       true
% 1.72/1.02  --brand_transform                       false
% 1.72/1.02  --non_eq_to_eq                          false
% 1.72/1.02  --prep_def_merge                        true
% 1.72/1.02  --prep_def_merge_prop_impl              false
% 1.72/1.02  --prep_def_merge_mbd                    true
% 1.72/1.02  --prep_def_merge_tr_red                 false
% 1.72/1.02  --prep_def_merge_tr_cl                  false
% 1.72/1.02  --smt_preprocessing                     true
% 1.72/1.02  --smt_ac_axioms                         fast
% 1.72/1.02  --preprocessed_out                      false
% 1.72/1.02  --preprocessed_stats                    false
% 1.72/1.02  
% 1.72/1.02  ------ Abstraction refinement Options
% 1.72/1.02  
% 1.72/1.02  --abstr_ref                             []
% 1.72/1.02  --abstr_ref_prep                        false
% 1.72/1.02  --abstr_ref_until_sat                   false
% 1.72/1.02  --abstr_ref_sig_restrict                funpre
% 1.72/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.72/1.02  --abstr_ref_under                       []
% 1.72/1.02  
% 1.72/1.02  ------ SAT Options
% 1.72/1.02  
% 1.72/1.02  --sat_mode                              false
% 1.72/1.02  --sat_fm_restart_options                ""
% 1.72/1.02  --sat_gr_def                            false
% 1.72/1.02  --sat_epr_types                         true
% 1.72/1.02  --sat_non_cyclic_types                  false
% 1.72/1.02  --sat_finite_models                     false
% 1.72/1.02  --sat_fm_lemmas                         false
% 1.72/1.02  --sat_fm_prep                           false
% 1.72/1.02  --sat_fm_uc_incr                        true
% 1.72/1.02  --sat_out_model                         small
% 1.72/1.02  --sat_out_clauses                       false
% 1.72/1.02  
% 1.72/1.02  ------ QBF Options
% 1.72/1.02  
% 1.72/1.02  --qbf_mode                              false
% 1.72/1.02  --qbf_elim_univ                         false
% 1.72/1.02  --qbf_dom_inst                          none
% 1.72/1.02  --qbf_dom_pre_inst                      false
% 1.72/1.02  --qbf_sk_in                             false
% 1.72/1.02  --qbf_pred_elim                         true
% 1.72/1.02  --qbf_split                             512
% 1.72/1.02  
% 1.72/1.02  ------ BMC1 Options
% 1.72/1.02  
% 1.72/1.02  --bmc1_incremental                      false
% 1.72/1.02  --bmc1_axioms                           reachable_all
% 1.72/1.02  --bmc1_min_bound                        0
% 1.72/1.02  --bmc1_max_bound                        -1
% 1.72/1.02  --bmc1_max_bound_default                -1
% 1.72/1.02  --bmc1_symbol_reachability              true
% 1.72/1.02  --bmc1_property_lemmas                  false
% 1.72/1.02  --bmc1_k_induction                      false
% 1.72/1.02  --bmc1_non_equiv_states                 false
% 1.72/1.02  --bmc1_deadlock                         false
% 1.72/1.02  --bmc1_ucm                              false
% 1.72/1.02  --bmc1_add_unsat_core                   none
% 1.72/1.02  --bmc1_unsat_core_children              false
% 1.72/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.72/1.02  --bmc1_out_stat                         full
% 1.72/1.02  --bmc1_ground_init                      false
% 1.72/1.02  --bmc1_pre_inst_next_state              false
% 1.72/1.02  --bmc1_pre_inst_state                   false
% 1.72/1.02  --bmc1_pre_inst_reach_state             false
% 1.72/1.02  --bmc1_out_unsat_core                   false
% 1.72/1.02  --bmc1_aig_witness_out                  false
% 1.72/1.02  --bmc1_verbose                          false
% 1.72/1.02  --bmc1_dump_clauses_tptp                false
% 1.72/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.72/1.02  --bmc1_dump_file                        -
% 1.72/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.72/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.72/1.02  --bmc1_ucm_extend_mode                  1
% 1.72/1.02  --bmc1_ucm_init_mode                    2
% 1.72/1.02  --bmc1_ucm_cone_mode                    none
% 1.72/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.72/1.02  --bmc1_ucm_relax_model                  4
% 1.72/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.72/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.72/1.02  --bmc1_ucm_layered_model                none
% 1.72/1.02  --bmc1_ucm_max_lemma_size               10
% 1.72/1.02  
% 1.72/1.02  ------ AIG Options
% 1.72/1.02  
% 1.72/1.02  --aig_mode                              false
% 1.72/1.02  
% 1.72/1.02  ------ Instantiation Options
% 1.72/1.02  
% 1.72/1.02  --instantiation_flag                    true
% 1.72/1.02  --inst_sos_flag                         false
% 1.72/1.02  --inst_sos_phase                        true
% 1.72/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.72/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.72/1.02  --inst_lit_sel_side                     none
% 1.72/1.02  --inst_solver_per_active                1400
% 1.72/1.02  --inst_solver_calls_frac                1.
% 1.72/1.02  --inst_passive_queue_type               priority_queues
% 1.72/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.72/1.02  --inst_passive_queues_freq              [25;2]
% 1.72/1.02  --inst_dismatching                      true
% 1.72/1.02  --inst_eager_unprocessed_to_passive     true
% 1.72/1.02  --inst_prop_sim_given                   true
% 1.72/1.02  --inst_prop_sim_new                     false
% 1.72/1.02  --inst_subs_new                         false
% 1.72/1.02  --inst_eq_res_simp                      false
% 1.72/1.02  --inst_subs_given                       false
% 1.72/1.02  --inst_orphan_elimination               true
% 1.72/1.02  --inst_learning_loop_flag               true
% 1.72/1.02  --inst_learning_start                   3000
% 1.72/1.02  --inst_learning_factor                  2
% 1.72/1.02  --inst_start_prop_sim_after_learn       3
% 1.72/1.02  --inst_sel_renew                        solver
% 1.72/1.02  --inst_lit_activity_flag                true
% 1.72/1.02  --inst_restr_to_given                   false
% 1.72/1.02  --inst_activity_threshold               500
% 1.72/1.02  --inst_out_proof                        true
% 1.72/1.02  
% 1.72/1.02  ------ Resolution Options
% 1.72/1.02  
% 1.72/1.02  --resolution_flag                       false
% 1.72/1.02  --res_lit_sel                           adaptive
% 1.72/1.02  --res_lit_sel_side                      none
% 1.72/1.02  --res_ordering                          kbo
% 1.72/1.02  --res_to_prop_solver                    active
% 1.72/1.02  --res_prop_simpl_new                    false
% 1.72/1.02  --res_prop_simpl_given                  true
% 1.72/1.02  --res_passive_queue_type                priority_queues
% 1.72/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.72/1.02  --res_passive_queues_freq               [15;5]
% 1.72/1.02  --res_forward_subs                      full
% 1.72/1.02  --res_backward_subs                     full
% 1.72/1.02  --res_forward_subs_resolution           true
% 1.72/1.02  --res_backward_subs_resolution          true
% 1.72/1.02  --res_orphan_elimination                true
% 1.72/1.02  --res_time_limit                        2.
% 1.72/1.02  --res_out_proof                         true
% 1.72/1.02  
% 1.72/1.02  ------ Superposition Options
% 1.72/1.02  
% 1.72/1.02  --superposition_flag                    true
% 1.72/1.02  --sup_passive_queue_type                priority_queues
% 1.72/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.72/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.72/1.02  --demod_completeness_check              fast
% 1.72/1.02  --demod_use_ground                      true
% 1.72/1.02  --sup_to_prop_solver                    passive
% 1.72/1.02  --sup_prop_simpl_new                    true
% 1.72/1.02  --sup_prop_simpl_given                  true
% 1.72/1.02  --sup_fun_splitting                     false
% 1.72/1.02  --sup_smt_interval                      50000
% 1.72/1.02  
% 1.72/1.02  ------ Superposition Simplification Setup
% 1.72/1.02  
% 1.72/1.02  --sup_indices_passive                   []
% 1.72/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.72/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.02  --sup_full_bw                           [BwDemod]
% 1.72/1.02  --sup_immed_triv                        [TrivRules]
% 1.72/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.72/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.02  --sup_immed_bw_main                     []
% 1.72/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.72/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/1.02  
% 1.72/1.02  ------ Combination Options
% 1.72/1.02  
% 1.72/1.02  --comb_res_mult                         3
% 1.72/1.02  --comb_sup_mult                         2
% 1.72/1.02  --comb_inst_mult                        10
% 1.72/1.02  
% 1.72/1.02  ------ Debug Options
% 1.72/1.02  
% 1.72/1.02  --dbg_backtrace                         false
% 1.72/1.02  --dbg_dump_prop_clauses                 false
% 1.72/1.02  --dbg_dump_prop_clauses_file            -
% 1.72/1.02  --dbg_out_stat                          false
% 1.72/1.02  
% 1.72/1.02  
% 1.72/1.02  
% 1.72/1.02  
% 1.72/1.02  ------ Proving...
% 1.72/1.02  
% 1.72/1.02  
% 1.72/1.02  % SZS status Theorem for theBenchmark.p
% 1.72/1.02  
% 1.72/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.72/1.02  
% 1.72/1.02  fof(f10,conjecture,(
% 1.72/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.02  
% 1.72/1.02  fof(f11,negated_conjecture,(
% 1.72/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.72/1.02    inference(negated_conjecture,[],[f10])).
% 1.72/1.02  
% 1.72/1.02  fof(f25,plain,(
% 1.72/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.72/1.02    inference(ennf_transformation,[],[f11])).
% 1.72/1.02  
% 1.72/1.02  fof(f26,plain,(
% 1.72/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.72/1.02    inference(flattening,[],[f25])).
% 1.72/1.02  
% 1.72/1.02  fof(f32,plain,(
% 1.72/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.72/1.02    inference(nnf_transformation,[],[f26])).
% 1.72/1.02  
% 1.72/1.02  fof(f33,plain,(
% 1.72/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.72/1.02    inference(flattening,[],[f32])).
% 1.72/1.02  
% 1.72/1.02  fof(f39,plain,(
% 1.72/1.02    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK5) | r1_tmap_1(X1,X0,X2,X4)) & sK5 = X4 & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 1.72/1.02    introduced(choice_axiom,[])).
% 1.72/1.02  
% 1.72/1.02  fof(f38,plain,(
% 1.72/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK4)) & sK4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 1.72/1.02    introduced(choice_axiom,[])).
% 1.72/1.02  
% 1.72/1.02  fof(f37,plain,(
% 1.72/1.02    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK3,X1) & v1_tsep_1(sK3,X1) & ~v2_struct_0(sK3))) )),
% 1.72/1.02    introduced(choice_axiom,[])).
% 1.72/1.02  
% 1.72/1.02  fof(f36,plain,(
% 1.72/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X5) | ~r1_tmap_1(X1,X0,sK2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X5) | r1_tmap_1(X1,X0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK2))) )),
% 1.72/1.02    introduced(choice_axiom,[])).
% 1.72/1.02  
% 1.72/1.02  fof(f35,plain,(
% 1.72/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X5) | ~r1_tmap_1(sK1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X5) | r1_tmap_1(sK1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.72/1.02    introduced(choice_axiom,[])).
% 1.72/1.02  
% 1.72/1.02  fof(f34,plain,(
% 1.72/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | ~r1_tmap_1(X1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | r1_tmap_1(X1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.72/1.02    introduced(choice_axiom,[])).
% 1.72/1.02  
% 1.72/1.02  fof(f40,plain,(
% 1.72/1.02    ((((((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.72/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f33,f39,f38,f37,f36,f35,f34])).
% 1.72/1.02  
% 1.72/1.02  fof(f66,plain,(
% 1.72/1.02    m1_pre_topc(sK3,sK1)),
% 1.72/1.02    inference(cnf_transformation,[],[f40])).
% 1.72/1.02  
% 1.72/1.02  fof(f9,axiom,(
% 1.72/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.02  
% 1.72/1.02  fof(f23,plain,(
% 1.72/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.72/1.02    inference(ennf_transformation,[],[f9])).
% 1.72/1.02  
% 1.72/1.02  fof(f24,plain,(
% 1.72/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/1.02    inference(flattening,[],[f23])).
% 1.72/1.02  
% 1.72/1.02  fof(f31,plain,(
% 1.72/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/1.02    inference(nnf_transformation,[],[f24])).
% 1.72/1.02  
% 1.72/1.02  fof(f53,plain,(
% 1.72/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.72/1.02    inference(cnf_transformation,[],[f31])).
% 1.72/1.02  
% 1.72/1.02  fof(f79,plain,(
% 1.72/1.02    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.72/1.02    inference(equality_resolution,[],[f53])).
% 1.72/1.02  
% 1.72/1.02  fof(f8,axiom,(
% 1.72/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 1.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.02  
% 1.72/1.02  fof(f21,plain,(
% 1.72/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.72/1.02    inference(ennf_transformation,[],[f8])).
% 1.72/1.02  
% 1.72/1.02  fof(f22,plain,(
% 1.72/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/1.02    inference(flattening,[],[f21])).
% 1.72/1.02  
% 1.72/1.02  fof(f52,plain,(
% 1.72/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.72/1.02    inference(cnf_transformation,[],[f22])).
% 1.72/1.02  
% 1.72/1.02  fof(f77,plain,(
% 1.72/1.02    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.72/1.02    inference(equality_resolution,[],[f52])).
% 1.72/1.02  
% 1.72/1.02  fof(f62,plain,(
% 1.72/1.02    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.72/1.02    inference(cnf_transformation,[],[f40])).
% 1.72/1.02  
% 1.72/1.02  fof(f61,plain,(
% 1.72/1.02    v1_funct_1(sK2)),
% 1.72/1.02    inference(cnf_transformation,[],[f40])).
% 1.72/1.02  
% 1.72/1.02  fof(f58,plain,(
% 1.72/1.02    ~v2_struct_0(sK1)),
% 1.72/1.02    inference(cnf_transformation,[],[f40])).
% 1.72/1.02  
% 1.72/1.02  fof(f59,plain,(
% 1.72/1.02    v2_pre_topc(sK1)),
% 1.72/1.02    inference(cnf_transformation,[],[f40])).
% 1.72/1.02  
% 1.72/1.02  fof(f60,plain,(
% 1.72/1.02    l1_pre_topc(sK1)),
% 1.72/1.02    inference(cnf_transformation,[],[f40])).
% 1.72/1.02  
% 1.72/1.02  fof(f64,plain,(
% 1.72/1.02    ~v2_struct_0(sK3)),
% 1.72/1.02    inference(cnf_transformation,[],[f40])).
% 1.72/1.02  
% 1.72/1.02  fof(f56,plain,(
% 1.72/1.02    v2_pre_topc(sK0)),
% 1.72/1.02    inference(cnf_transformation,[],[f40])).
% 1.72/1.02  
% 1.72/1.02  fof(f55,plain,(
% 1.72/1.02    ~v2_struct_0(sK0)),
% 1.72/1.02    inference(cnf_transformation,[],[f40])).
% 1.72/1.02  
% 1.72/1.02  fof(f57,plain,(
% 1.72/1.02    l1_pre_topc(sK0)),
% 1.72/1.02    inference(cnf_transformation,[],[f40])).
% 1.72/1.02  
% 1.72/1.02  fof(f63,plain,(
% 1.72/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.72/1.02    inference(cnf_transformation,[],[f40])).
% 1.72/1.02  
% 1.72/1.02  fof(f71,plain,(
% 1.72/1.02    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 1.72/1.02    inference(cnf_transformation,[],[f40])).
% 1.72/1.02  
% 1.72/1.02  fof(f69,plain,(
% 1.72/1.02    sK4 = sK5),
% 1.72/1.02    inference(cnf_transformation,[],[f40])).
% 1.72/1.02  
% 1.72/1.02  fof(f3,axiom,(
% 1.72/1.02    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.02  
% 1.72/1.02  fof(f14,plain,(
% 1.72/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.72/1.02    inference(ennf_transformation,[],[f3])).
% 1.72/1.02  
% 1.72/1.02  fof(f45,plain,(
% 1.72/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.72/1.02    inference(cnf_transformation,[],[f14])).
% 1.72/1.02  
% 1.72/1.02  fof(f5,axiom,(
% 1.72/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.02  
% 1.72/1.02  fof(f16,plain,(
% 1.72/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.72/1.02    inference(ennf_transformation,[],[f5])).
% 1.72/1.02  
% 1.72/1.02  fof(f17,plain,(
% 1.72/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.72/1.02    inference(flattening,[],[f16])).
% 1.72/1.02  
% 1.72/1.02  fof(f47,plain,(
% 1.72/1.02    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.72/1.02    inference(cnf_transformation,[],[f17])).
% 1.72/1.02  
% 1.72/1.02  fof(f4,axiom,(
% 1.72/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.02  
% 1.72/1.02  fof(f15,plain,(
% 1.72/1.02    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.72/1.02    inference(ennf_transformation,[],[f4])).
% 1.72/1.02  
% 1.72/1.02  fof(f46,plain,(
% 1.72/1.02    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.72/1.02    inference(cnf_transformation,[],[f15])).
% 1.72/1.02  
% 1.72/1.02  fof(f2,axiom,(
% 1.72/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.03  
% 1.72/1.03  fof(f12,plain,(
% 1.72/1.03    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.72/1.03    inference(ennf_transformation,[],[f2])).
% 1.72/1.03  
% 1.72/1.03  fof(f13,plain,(
% 1.72/1.03    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.72/1.03    inference(flattening,[],[f12])).
% 1.72/1.03  
% 1.72/1.03  fof(f44,plain,(
% 1.72/1.03    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.72/1.03    inference(cnf_transformation,[],[f13])).
% 1.72/1.03  
% 1.72/1.03  fof(f54,plain,(
% 1.72/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.72/1.03    inference(cnf_transformation,[],[f31])).
% 1.72/1.03  
% 1.72/1.03  fof(f78,plain,(
% 1.72/1.03    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.72/1.03    inference(equality_resolution,[],[f54])).
% 1.72/1.03  
% 1.72/1.03  fof(f6,axiom,(
% 1.72/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.72/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.03  
% 1.72/1.03  fof(f18,plain,(
% 1.72/1.03    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.72/1.03    inference(ennf_transformation,[],[f6])).
% 1.72/1.03  
% 1.72/1.03  fof(f19,plain,(
% 1.72/1.03    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.72/1.03    inference(flattening,[],[f18])).
% 1.72/1.03  
% 1.72/1.03  fof(f29,plain,(
% 1.72/1.03    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.72/1.03    inference(nnf_transformation,[],[f19])).
% 1.72/1.03  
% 1.72/1.03  fof(f30,plain,(
% 1.72/1.03    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.72/1.03    inference(flattening,[],[f29])).
% 1.72/1.03  
% 1.72/1.03  fof(f48,plain,(
% 1.72/1.03    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.72/1.03    inference(cnf_transformation,[],[f30])).
% 1.72/1.03  
% 1.72/1.03  fof(f76,plain,(
% 1.72/1.03    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.72/1.03    inference(equality_resolution,[],[f48])).
% 1.72/1.03  
% 1.72/1.03  fof(f7,axiom,(
% 1.72/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.72/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.03  
% 1.72/1.03  fof(f20,plain,(
% 1.72/1.03    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.72/1.03    inference(ennf_transformation,[],[f7])).
% 1.72/1.03  
% 1.72/1.03  fof(f51,plain,(
% 1.72/1.03    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.72/1.03    inference(cnf_transformation,[],[f20])).
% 1.72/1.03  
% 1.72/1.03  fof(f65,plain,(
% 1.72/1.03    v1_tsep_1(sK3,sK1)),
% 1.72/1.03    inference(cnf_transformation,[],[f40])).
% 1.72/1.03  
% 1.72/1.03  fof(f1,axiom,(
% 1.72/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.72/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.03  
% 1.72/1.03  fof(f27,plain,(
% 1.72/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.72/1.03    inference(nnf_transformation,[],[f1])).
% 1.72/1.03  
% 1.72/1.03  fof(f28,plain,(
% 1.72/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.72/1.03    inference(flattening,[],[f27])).
% 1.72/1.03  
% 1.72/1.03  fof(f42,plain,(
% 1.72/1.03    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.72/1.03    inference(cnf_transformation,[],[f28])).
% 1.72/1.03  
% 1.72/1.03  fof(f72,plain,(
% 1.72/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.72/1.03    inference(equality_resolution,[],[f42])).
% 1.72/1.03  
% 1.72/1.03  fof(f67,plain,(
% 1.72/1.03    m1_subset_1(sK4,u1_struct_0(sK1))),
% 1.72/1.03    inference(cnf_transformation,[],[f40])).
% 1.72/1.03  
% 1.72/1.03  fof(f70,plain,(
% 1.72/1.03    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 1.72/1.03    inference(cnf_transformation,[],[f40])).
% 1.72/1.03  
% 1.72/1.03  fof(f68,plain,(
% 1.72/1.03    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.72/1.03    inference(cnf_transformation,[],[f40])).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1331,plain,( X0 = X0 ),theory(equality) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2253,plain,
% 1.72/1.03      ( k2_tmap_1(sK1,sK0,sK2,sK3) = k2_tmap_1(sK1,sK0,sK2,sK3) ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_1331]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1337,plain,
% 1.72/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.72/1.03      | r1_tmap_1(X4,X5,X6,X7)
% 1.72/1.03      | X4 != X0
% 1.72/1.03      | X5 != X1
% 1.72/1.03      | X6 != X2
% 1.72/1.03      | X7 != X3 ),
% 1.72/1.03      theory(equality) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1850,plain,
% 1.72/1.03      ( r1_tmap_1(X0,X1,X2,X3)
% 1.72/1.03      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.72/1.03      | X2 != k2_tmap_1(sK1,sK0,sK2,sK3)
% 1.72/1.03      | X3 != sK5
% 1.72/1.03      | X1 != sK0
% 1.72/1.03      | X0 != sK3 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_1337]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1905,plain,
% 1.72/1.03      ( r1_tmap_1(X0,X1,X2,sK4)
% 1.72/1.03      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.72/1.03      | X2 != k2_tmap_1(sK1,sK0,sK2,sK3)
% 1.72/1.03      | X1 != sK0
% 1.72/1.03      | X0 != sK3
% 1.72/1.03      | sK4 != sK5 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_1850]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1951,plain,
% 1.72/1.03      ( r1_tmap_1(X0,sK0,X1,sK4)
% 1.72/1.03      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.72/1.03      | X1 != k2_tmap_1(sK1,sK0,sK2,sK3)
% 1.72/1.03      | X0 != sK3
% 1.72/1.03      | sK4 != sK5
% 1.72/1.03      | sK0 != sK0 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_1905]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2119,plain,
% 1.72/1.03      ( r1_tmap_1(sK3,sK0,X0,sK4)
% 1.72/1.03      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.72/1.03      | X0 != k2_tmap_1(sK1,sK0,sK2,sK3)
% 1.72/1.03      | sK4 != sK5
% 1.72/1.03      | sK0 != sK0
% 1.72/1.03      | sK3 != sK3 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_1951]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2252,plain,
% 1.72/1.03      ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
% 1.72/1.03      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.72/1.03      | k2_tmap_1(sK1,sK0,sK2,sK3) != k2_tmap_1(sK1,sK0,sK2,sK3)
% 1.72/1.03      | sK4 != sK5
% 1.72/1.03      | sK0 != sK0
% 1.72/1.03      | sK3 != sK3 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_2119]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2120,plain,
% 1.72/1.03      ( sK3 = sK3 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_1331]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_19,negated_conjecture,
% 1.72/1.03      ( m1_pre_topc(sK3,sK1) ),
% 1.72/1.03      inference(cnf_transformation,[],[f66]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_13,plain,
% 1.72/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.72/1.03      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.72/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.72/1.03      | ~ v3_pre_topc(X5,X0)
% 1.72/1.03      | ~ m1_pre_topc(X4,X0)
% 1.72/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.72/1.03      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/1.03      | ~ r2_hidden(X3,X5)
% 1.72/1.03      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.72/1.03      | ~ v1_funct_1(X2)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | ~ v2_pre_topc(X0)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | v2_struct_0(X4)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | ~ l1_pre_topc(X0) ),
% 1.72/1.03      inference(cnf_transformation,[],[f79]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_11,plain,
% 1.72/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.72/1.03      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.72/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.72/1.03      | ~ m1_pre_topc(X4,X0)
% 1.72/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/1.03      | ~ v1_funct_1(X2)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | ~ v2_pre_topc(X0)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | v2_struct_0(X4)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | ~ l1_pre_topc(X0) ),
% 1.72/1.03      inference(cnf_transformation,[],[f77]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_160,plain,
% 1.72/1.03      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.72/1.03      | ~ m1_pre_topc(X4,X0)
% 1.72/1.03      | ~ r1_tmap_1(X0,X1,X2,X3)
% 1.72/1.03      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.72/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/1.03      | ~ v1_funct_1(X2)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | ~ v2_pre_topc(X0)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | v2_struct_0(X4)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | ~ l1_pre_topc(X0) ),
% 1.72/1.03      inference(global_propositional_subsumption,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_13,c_11]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_161,plain,
% 1.72/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.72/1.03      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.72/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.72/1.03      | ~ m1_pre_topc(X4,X0)
% 1.72/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/1.03      | ~ v1_funct_1(X2)
% 1.72/1.03      | ~ v2_pre_topc(X0)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | v2_struct_0(X4)
% 1.72/1.03      | ~ l1_pre_topc(X0)
% 1.72/1.03      | ~ l1_pre_topc(X1) ),
% 1.72/1.03      inference(renaming,[status(thm)],[c_160]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_23,negated_conjecture,
% 1.72/1.03      ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 1.72/1.03      inference(cnf_transformation,[],[f62]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_609,plain,
% 1.72/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.72/1.03      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.72/1.03      | ~ m1_pre_topc(X4,X0)
% 1.72/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/1.03      | ~ v1_funct_1(X2)
% 1.72/1.03      | ~ v2_pre_topc(X0)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | v2_struct_0(X4)
% 1.72/1.03      | ~ l1_pre_topc(X0)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.72/1.03      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.72/1.03      | sK2 != X2 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_161,c_23]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_610,plain,
% 1.72/1.03      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.72/1.03      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.72/1.03      | ~ m1_pre_topc(X0,X2)
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.72/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.72/1.03      | ~ v1_funct_1(sK2)
% 1.72/1.03      | ~ v2_pre_topc(X2)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | v2_struct_0(X2)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | ~ l1_pre_topc(X2)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.72/1.03      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_609]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_24,negated_conjecture,
% 1.72/1.03      ( v1_funct_1(sK2) ),
% 1.72/1.03      inference(cnf_transformation,[],[f61]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_614,plain,
% 1.72/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/1.03      | ~ m1_pre_topc(X0,X2)
% 1.72/1.03      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.72/1.03      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.72/1.03      | ~ v2_pre_topc(X2)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | v2_struct_0(X2)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | ~ l1_pre_topc(X2)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.72/1.03      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.72/1.03      inference(global_propositional_subsumption,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_610,c_24]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_615,plain,
% 1.72/1.03      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.72/1.03      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.72/1.03      | ~ m1_pre_topc(X0,X2)
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.72/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | ~ v2_pre_topc(X2)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | v2_struct_0(X2)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | ~ l1_pre_topc(X2)
% 1.72/1.03      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.72/1.03      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.72/1.03      inference(renaming,[status(thm)],[c_614]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_855,plain,
% 1.72/1.03      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.72/1.03      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.72/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.72/1.03      | ~ v2_pre_topc(X2)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | v2_struct_0(X2)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | ~ l1_pre_topc(X2)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.72/1.03      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.72/1.03      | sK1 != X2
% 1.72/1.03      | sK3 != X0 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_615]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_856,plain,
% 1.72/1.03      ( ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.72/1.03      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.72/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.72/1.03      | ~ v2_pre_topc(X0)
% 1.72/1.03      | ~ v2_pre_topc(sK1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | v2_struct_0(sK1)
% 1.72/1.03      | v2_struct_0(sK3)
% 1.72/1.03      | ~ l1_pre_topc(X0)
% 1.72/1.03      | ~ l1_pre_topc(sK1)
% 1.72/1.03      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.72/1.03      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_855]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_27,negated_conjecture,
% 1.72/1.03      ( ~ v2_struct_0(sK1) ),
% 1.72/1.03      inference(cnf_transformation,[],[f58]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_26,negated_conjecture,
% 1.72/1.03      ( v2_pre_topc(sK1) ),
% 1.72/1.03      inference(cnf_transformation,[],[f59]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_25,negated_conjecture,
% 1.72/1.03      ( l1_pre_topc(sK1) ),
% 1.72/1.03      inference(cnf_transformation,[],[f60]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_21,negated_conjecture,
% 1.72/1.03      ( ~ v2_struct_0(sK3) ),
% 1.72/1.03      inference(cnf_transformation,[],[f64]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_860,plain,
% 1.72/1.03      ( ~ l1_pre_topc(X0)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.72/1.03      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.72/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.72/1.03      | ~ v2_pre_topc(X0)
% 1.72/1.03      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.72/1.03      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.72/1.03      inference(global_propositional_subsumption,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_856,c_27,c_26,c_25,c_21]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_861,plain,
% 1.72/1.03      ( ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.72/1.03      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.72/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.72/1.03      | ~ v2_pre_topc(X0)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | ~ l1_pre_topc(X0)
% 1.72/1.03      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.72/1.03      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.72/1.03      inference(renaming,[status(thm)],[c_860]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_29,negated_conjecture,
% 1.72/1.03      ( v2_pre_topc(sK0) ),
% 1.72/1.03      inference(cnf_transformation,[],[f56]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1104,plain,
% 1.72/1.03      ( ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.72/1.03      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.72/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | ~ l1_pre_topc(X0)
% 1.72/1.03      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.72/1.03      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.72/1.03      | sK0 != X0 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_861,c_29]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1105,plain,
% 1.72/1.03      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
% 1.72/1.03      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.72/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.72/1.03      | v2_struct_0(sK0)
% 1.72/1.03      | ~ l1_pre_topc(sK0)
% 1.72/1.03      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_1104]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_30,negated_conjecture,
% 1.72/1.03      ( ~ v2_struct_0(sK0) ),
% 1.72/1.03      inference(cnf_transformation,[],[f55]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_28,negated_conjecture,
% 1.72/1.03      ( l1_pre_topc(sK0) ),
% 1.72/1.03      inference(cnf_transformation,[],[f57]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_22,negated_conjecture,
% 1.72/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 1.72/1.03      inference(cnf_transformation,[],[f63]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1109,plain,
% 1.72/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.72/1.03      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.72/1.03      | ~ r1_tmap_1(sK1,sK0,sK2,X0)
% 1.72/1.03      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.72/1.03      inference(global_propositional_subsumption,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_1105,c_30,c_28,c_22]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1110,plain,
% 1.72/1.03      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
% 1.72/1.03      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.72/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.72/1.03      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.72/1.03      inference(renaming,[status(thm)],[c_1109]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1223,plain,
% 1.72/1.03      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
% 1.72/1.03      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.72/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.72/1.03      inference(equality_resolution_simp,[status(thm)],[c_1110]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1690,plain,
% 1.72/1.03      ( r1_tmap_1(sK1,sK0,sK2,X0) != iProver_top
% 1.72/1.03      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) = iProver_top
% 1.72/1.03      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 1.72/1.03      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_1223]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_14,negated_conjecture,
% 1.72/1.03      ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
% 1.72/1.03      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.72/1.03      inference(cnf_transformation,[],[f71]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1701,plain,
% 1.72/1.03      ( r1_tmap_1(sK1,sK0,sK2,sK4) != iProver_top
% 1.72/1.03      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_16,negated_conjecture,
% 1.72/1.03      ( sK4 = sK5 ),
% 1.72/1.03      inference(cnf_transformation,[],[f69]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1728,plain,
% 1.72/1.03      ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
% 1.72/1.03      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
% 1.72/1.03      inference(light_normalisation,[status(thm)],[c_1701,c_16]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2003,plain,
% 1.72/1.03      ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
% 1.72/1.03      | m1_subset_1(sK5,u1_struct_0(sK1)) != iProver_top
% 1.72/1.03      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
% 1.72/1.03      inference(superposition,[status(thm)],[c_1690,c_1728]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2004,plain,
% 1.72/1.03      ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.72/1.03      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 1.72/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_2003]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1952,plain,
% 1.72/1.03      ( sK0 = sK0 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_1331]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1936,plain,
% 1.72/1.03      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_1331]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1333,plain,
% 1.72/1.03      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.72/1.03      theory(equality) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1826,plain,
% 1.72/1.03      ( m1_subset_1(X0,X1)
% 1.72/1.03      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.72/1.03      | X1 != u1_struct_0(sK3)
% 1.72/1.03      | X0 != sK5 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_1333]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1865,plain,
% 1.72/1.03      ( m1_subset_1(sK4,X0)
% 1.72/1.03      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.72/1.03      | X0 != u1_struct_0(sK3)
% 1.72/1.03      | sK4 != sK5 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_1826]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1935,plain,
% 1.72/1.03      ( m1_subset_1(sK4,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.72/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.72/1.03      | sK4 != sK5 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_1865]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_4,plain,
% 1.72/1.03      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.72/1.03      inference(cnf_transformation,[],[f45]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_6,plain,
% 1.72/1.03      ( v2_struct_0(X0)
% 1.72/1.03      | ~ l1_struct_0(X0)
% 1.72/1.03      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.72/1.03      inference(cnf_transformation,[],[f47]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_385,plain,
% 1.72/1.03      ( v2_struct_0(X0)
% 1.72/1.03      | ~ l1_pre_topc(X0)
% 1.72/1.03      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.72/1.03      inference(resolution,[status(thm)],[c_4,c_6]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_5,plain,
% 1.72/1.03      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.72/1.03      inference(cnf_transformation,[],[f46]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_844,plain,
% 1.72/1.03      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK1 != X0 | sK3 != X1 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_5,c_19]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_845,plain,
% 1.72/1.03      ( ~ l1_pre_topc(sK1) | l1_pre_topc(sK3) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_844]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_847,plain,
% 1.72/1.03      ( l1_pre_topc(sK3) ),
% 1.72/1.03      inference(global_propositional_subsumption,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_845,c_25]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1181,plain,
% 1.72/1.03      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_385,c_847]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1182,plain,
% 1.72/1.03      ( v2_struct_0(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_1181]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1184,plain,
% 1.72/1.03      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.72/1.03      inference(global_propositional_subsumption,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_1182,c_21]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_3,plain,
% 1.72/1.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.72/1.03      inference(cnf_transformation,[],[f44]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_12,plain,
% 1.72/1.03      ( r1_tmap_1(X0,X1,X2,X3)
% 1.72/1.03      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.72/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.72/1.03      | ~ v3_pre_topc(X5,X0)
% 1.72/1.03      | ~ m1_pre_topc(X4,X0)
% 1.72/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.72/1.03      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/1.03      | ~ r2_hidden(X3,X5)
% 1.72/1.03      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.72/1.03      | ~ v1_funct_1(X2)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | ~ v2_pre_topc(X0)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | v2_struct_0(X4)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | ~ l1_pre_topc(X0) ),
% 1.72/1.03      inference(cnf_transformation,[],[f78]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_9,plain,
% 1.72/1.03      ( ~ v1_tsep_1(X0,X1)
% 1.72/1.03      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.72/1.03      | ~ m1_pre_topc(X0,X1)
% 1.72/1.03      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | ~ l1_pre_topc(X1) ),
% 1.72/1.03      inference(cnf_transformation,[],[f76]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_10,plain,
% 1.72/1.03      ( ~ m1_pre_topc(X0,X1)
% 1.72/1.03      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.72/1.03      | ~ l1_pre_topc(X1) ),
% 1.72/1.03      inference(cnf_transformation,[],[f51]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_168,plain,
% 1.72/1.03      ( ~ m1_pre_topc(X0,X1)
% 1.72/1.03      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.72/1.03      | ~ v1_tsep_1(X0,X1)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | ~ l1_pre_topc(X1) ),
% 1.72/1.03      inference(global_propositional_subsumption,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_9,c_10]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_169,plain,
% 1.72/1.03      ( ~ v1_tsep_1(X0,X1)
% 1.72/1.03      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.72/1.03      | ~ m1_pre_topc(X0,X1)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | ~ l1_pre_topc(X1) ),
% 1.72/1.03      inference(renaming,[status(thm)],[c_168]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_20,negated_conjecture,
% 1.72/1.03      ( v1_tsep_1(sK3,sK1) ),
% 1.72/1.03      inference(cnf_transformation,[],[f65]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_426,plain,
% 1.72/1.03      ( v3_pre_topc(u1_struct_0(X0),X1)
% 1.72/1.03      | ~ m1_pre_topc(X0,X1)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | sK1 != X1
% 1.72/1.03      | sK3 != X0 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_169,c_20]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_427,plain,
% 1.72/1.03      ( v3_pre_topc(u1_struct_0(sK3),sK1)
% 1.72/1.03      | ~ m1_pre_topc(sK3,sK1)
% 1.72/1.03      | ~ v2_pre_topc(sK1)
% 1.72/1.03      | ~ l1_pre_topc(sK1) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_426]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_429,plain,
% 1.72/1.03      ( v3_pre_topc(u1_struct_0(sK3),sK1) ),
% 1.72/1.03      inference(global_propositional_subsumption,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_427,c_26,c_25,c_19]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_439,plain,
% 1.72/1.03      ( r1_tmap_1(X0,X1,X2,X3)
% 1.72/1.03      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.72/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.72/1.03      | ~ m1_pre_topc(X4,X0)
% 1.72/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.72/1.03      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/1.03      | ~ r2_hidden(X3,X5)
% 1.72/1.03      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.72/1.03      | ~ v1_funct_1(X2)
% 1.72/1.03      | ~ v2_pre_topc(X0)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | v2_struct_0(X4)
% 1.72/1.03      | ~ l1_pre_topc(X0)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | u1_struct_0(sK3) != X5
% 1.72/1.03      | sK1 != X0 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_429]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_440,plain,
% 1.72/1.03      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.72/1.03      | r1_tmap_1(sK1,X1,X2,X3)
% 1.72/1.03      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.72/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.72/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.72/1.03      | ~ r2_hidden(X3,u1_struct_0(sK3))
% 1.72/1.03      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.72/1.03      | ~ v1_funct_1(X2)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | ~ v2_pre_topc(sK1)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | v2_struct_0(sK1)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | ~ l1_pre_topc(sK1) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_439]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_444,plain,
% 1.72/1.03      ( ~ l1_pre_topc(X1)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | ~ v1_funct_1(X2)
% 1.72/1.03      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.72/1.03      | ~ r2_hidden(X3,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.72/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.72/1.03      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.72/1.03      | r1_tmap_1(sK1,X1,X2,X3)
% 1.72/1.03      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | v2_struct_0(X0) ),
% 1.72/1.03      inference(global_propositional_subsumption,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_440,c_27,c_26,c_25]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_445,plain,
% 1.72/1.03      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.72/1.03      | r1_tmap_1(sK1,X1,X2,X3)
% 1.72/1.03      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.72/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.72/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.72/1.03      | ~ r2_hidden(X3,u1_struct_0(sK3))
% 1.72/1.03      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.72/1.03      | ~ v1_funct_1(X2)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | ~ l1_pre_topc(X1) ),
% 1.72/1.03      inference(renaming,[status(thm)],[c_444]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_495,plain,
% 1.72/1.03      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.72/1.03      | r1_tmap_1(sK1,X1,X2,X3)
% 1.72/1.03      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.72/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.72/1.03      | ~ m1_subset_1(X4,X5)
% 1.72/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.72/1.03      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.72/1.03      | ~ v1_funct_1(X2)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | v1_xboole_0(X5)
% 1.72/1.03      | X3 != X4
% 1.72/1.03      | u1_struct_0(sK3) != X5 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_3,c_445]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_496,plain,
% 1.72/1.03      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.72/1.03      | r1_tmap_1(sK1,X1,X2,X3)
% 1.72/1.03      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.72/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.72/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.72/1.03      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.72/1.03      | ~ v1_funct_1(X2)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_495]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_718,plain,
% 1.72/1.03      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.72/1.03      | r1_tmap_1(sK1,X1,X2,X3)
% 1.72/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.72/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.72/1.03      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.72/1.03      | ~ v1_funct_1(X2)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | v1_xboole_0(u1_struct_0(sK3))
% 1.72/1.03      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.72/1.03      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.72/1.03      | sK2 != X2 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_23,c_496]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_719,plain,
% 1.72/1.03      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
% 1.72/1.03      | r1_tmap_1(sK1,X1,sK2,X2)
% 1.72/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.72/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.72/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.72/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.72/1.03      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.72/1.03      | ~ v1_funct_1(sK2)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | v1_xboole_0(u1_struct_0(sK3))
% 1.72/1.03      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_718]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_723,plain,
% 1.72/1.03      ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.72/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.72/1.03      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.72/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.72/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.72/1.03      | r1_tmap_1(sK1,X1,sK2,X2)
% 1.72/1.03      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | v1_xboole_0(u1_struct_0(sK3))
% 1.72/1.03      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.72/1.03      inference(global_propositional_subsumption,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_719,c_24]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_724,plain,
% 1.72/1.03      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
% 1.72/1.03      | r1_tmap_1(sK1,X1,sK2,X2)
% 1.72/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.72/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.72/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.72/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.72/1.03      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | v1_xboole_0(u1_struct_0(sK3))
% 1.72/1.03      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.72/1.03      inference(renaming,[status(thm)],[c_723]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_897,plain,
% 1.72/1.03      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
% 1.72/1.03      | r1_tmap_1(sK1,X1,sK2,X2)
% 1.72/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.72/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.72/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.72/1.03      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.72/1.03      | ~ v2_pre_topc(X1)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | v2_struct_0(X1)
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | v1_xboole_0(u1_struct_0(sK3))
% 1.72/1.03      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.72/1.03      | sK1 != sK1
% 1.72/1.03      | sK3 != X0 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_724]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_898,plain,
% 1.72/1.03      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.72/1.03      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.72/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.72/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.72/1.03      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
% 1.72/1.03      | ~ v2_pre_topc(X0)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | v2_struct_0(sK3)
% 1.72/1.03      | ~ l1_pre_topc(X0)
% 1.72/1.03      | v1_xboole_0(u1_struct_0(sK3))
% 1.72/1.03      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_897]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_833,plain,
% 1.72/1.03      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.72/1.03      | ~ l1_pre_topc(X1)
% 1.72/1.03      | sK1 != X1
% 1.72/1.03      | sK3 != X0 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_834,plain,
% 1.72/1.03      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.72/1.03      | ~ l1_pre_topc(sK1) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_833]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_902,plain,
% 1.72/1.03      ( v2_struct_0(X0)
% 1.72/1.03      | ~ v2_pre_topc(X0)
% 1.72/1.03      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.72/1.03      | r1_tmap_1(sK1,X0,sK2,X1)
% 1.72/1.03      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.72/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.72/1.03      | ~ l1_pre_topc(X0)
% 1.72/1.03      | v1_xboole_0(u1_struct_0(sK3))
% 1.72/1.03      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.72/1.03      inference(global_propositional_subsumption,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_898,c_25,c_21,c_834]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_903,plain,
% 1.72/1.03      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.72/1.03      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.72/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.72/1.03      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
% 1.72/1.03      | ~ v2_pre_topc(X0)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | ~ l1_pre_topc(X0)
% 1.72/1.03      | v1_xboole_0(u1_struct_0(sK3))
% 1.72/1.03      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.72/1.03      inference(renaming,[status(thm)],[c_902]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1,plain,
% 1.72/1.03      ( r1_tarski(X0,X0) ),
% 1.72/1.03      inference(cnf_transformation,[],[f72]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_930,plain,
% 1.72/1.03      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.72/1.03      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.72/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.72/1.03      | ~ v2_pre_topc(X0)
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | ~ l1_pre_topc(X0)
% 1.72/1.03      | v1_xboole_0(u1_struct_0(sK3))
% 1.72/1.03      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.72/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_903,c_1]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1074,plain,
% 1.72/1.03      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.72/1.03      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.72/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.72/1.03      | v2_struct_0(X0)
% 1.72/1.03      | ~ l1_pre_topc(X0)
% 1.72/1.03      | v1_xboole_0(u1_struct_0(sK3))
% 1.72/1.03      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.72/1.03      | sK0 != X0 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_930,c_29]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1075,plain,
% 1.72/1.03      ( r1_tmap_1(sK1,sK0,sK2,X0)
% 1.72/1.03      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.72/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.72/1.03      | v2_struct_0(sK0)
% 1.72/1.03      | ~ l1_pre_topc(sK0)
% 1.72/1.03      | v1_xboole_0(u1_struct_0(sK3))
% 1.72/1.03      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_1074]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1079,plain,
% 1.72/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.72/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.72/1.03      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.72/1.03      | r1_tmap_1(sK1,sK0,sK2,X0)
% 1.72/1.03      | v1_xboole_0(u1_struct_0(sK3))
% 1.72/1.03      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.72/1.03      inference(global_propositional_subsumption,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_1075,c_30,c_28,c_22]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1080,plain,
% 1.72/1.03      ( r1_tmap_1(sK1,sK0,sK2,X0)
% 1.72/1.03      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.72/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.72/1.03      | v1_xboole_0(u1_struct_0(sK3))
% 1.72/1.03      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.72/1.03      inference(renaming,[status(thm)],[c_1079]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1198,plain,
% 1.72/1.03      ( r1_tmap_1(sK1,sK0,sK2,X0)
% 1.72/1.03      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.72/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.72/1.03      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.72/1.03      inference(backward_subsumption_resolution,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_1184,c_1080]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1218,plain,
% 1.72/1.03      ( r1_tmap_1(sK1,sK0,sK2,X0)
% 1.72/1.03      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.72/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.72/1.03      inference(equality_resolution_simp,[status(thm)],[c_1198]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1817,plain,
% 1.72/1.03      ( r1_tmap_1(sK1,sK0,sK2,sK4)
% 1.72/1.03      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
% 1.72/1.03      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
% 1.72/1.03      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_1218]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_18,negated_conjecture,
% 1.72/1.03      ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
% 1.72/1.03      inference(cnf_transformation,[],[f67]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1698,plain,
% 1.72/1.03      ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1708,plain,
% 1.72/1.03      ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 1.72/1.03      inference(light_normalisation,[status(thm)],[c_1698,c_16]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1785,plain,
% 1.72/1.03      ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
% 1.72/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_1708]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_15,negated_conjecture,
% 1.72/1.03      ( r1_tmap_1(sK1,sK0,sK2,sK4)
% 1.72/1.03      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.72/1.03      inference(cnf_transformation,[],[f70]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1700,plain,
% 1.72/1.03      ( r1_tmap_1(sK1,sK0,sK2,sK4) = iProver_top
% 1.72/1.03      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1723,plain,
% 1.72/1.03      ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
% 1.72/1.03      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
% 1.72/1.03      inference(light_normalisation,[status(thm)],[c_1700,c_16]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1781,plain,
% 1.72/1.03      ( r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.72/1.03      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.72/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_1723]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_17,negated_conjecture,
% 1.72/1.03      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 1.72/1.03      inference(cnf_transformation,[],[f68]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(contradiction,plain,
% 1.72/1.03      ( $false ),
% 1.72/1.03      inference(minisat,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_2253,c_2252,c_2120,c_2004,c_1952,c_1936,c_1935,c_1817,
% 1.72/1.03                 c_1785,c_1781,c_14,c_16,c_17,c_18]) ).
% 1.72/1.03  
% 1.72/1.03  
% 1.72/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.72/1.03  
% 1.72/1.03  ------                               Statistics
% 1.72/1.03  
% 1.72/1.03  ------ General
% 1.72/1.03  
% 1.72/1.03  abstr_ref_over_cycles:                  0
% 1.72/1.03  abstr_ref_under_cycles:                 0
% 1.72/1.03  gc_basic_clause_elim:                   0
% 1.72/1.03  forced_gc_time:                         0
% 1.72/1.03  parsing_time:                           0.011
% 1.72/1.03  unif_index_cands_time:                  0.
% 1.72/1.03  unif_index_add_time:                    0.
% 1.72/1.03  orderings_time:                         0.
% 1.72/1.03  out_proof_time:                         0.02
% 1.72/1.03  total_time:                             0.119
% 1.72/1.03  num_of_symbols:                         57
% 1.72/1.03  num_of_terms:                           1503
% 1.72/1.03  
% 1.72/1.03  ------ Preprocessing
% 1.72/1.03  
% 1.72/1.03  num_of_splits:                          2
% 1.72/1.03  num_of_split_atoms:                     2
% 1.72/1.03  num_of_reused_defs:                     0
% 1.72/1.03  num_eq_ax_congr_red:                    9
% 1.72/1.03  num_of_sem_filtered_clauses:            1
% 1.72/1.03  num_of_subtypes:                        0
% 1.72/1.03  monotx_restored_types:                  0
% 1.72/1.03  sat_num_of_epr_types:                   0
% 1.72/1.03  sat_num_of_non_cyclic_types:            0
% 1.72/1.03  sat_guarded_non_collapsed_types:        0
% 1.72/1.03  num_pure_diseq_elim:                    0
% 1.72/1.03  simp_replaced_by:                       0
% 1.72/1.03  res_preprocessed:                       89
% 1.72/1.03  prep_upred:                             0
% 1.72/1.03  prep_unflattend:                        24
% 1.72/1.03  smt_new_axioms:                         0
% 1.72/1.03  pred_elim_cands:                        3
% 1.72/1.03  pred_elim:                              11
% 1.72/1.03  pred_elim_cl:                           16
% 1.72/1.03  pred_elim_cycles:                       17
% 1.72/1.03  merged_defs:                            8
% 1.72/1.03  merged_defs_ncl:                        0
% 1.72/1.03  bin_hyper_res:                          8
% 1.72/1.03  prep_cycles:                            4
% 1.72/1.03  pred_elim_time:                         0.029
% 1.72/1.03  splitting_time:                         0.
% 1.72/1.03  sem_filter_time:                        0.
% 1.72/1.03  monotx_time:                            0.
% 1.72/1.03  subtype_inf_time:                       0.
% 1.72/1.03  
% 1.72/1.03  ------ Problem properties
% 1.72/1.03  
% 1.72/1.03  clauses:                                15
% 1.72/1.03  conjectures:                            6
% 1.72/1.03  epr:                                    3
% 1.72/1.03  horn:                                   14
% 1.72/1.03  ground:                                 9
% 1.72/1.03  unary:                                  6
% 1.72/1.03  binary:                                 2
% 1.72/1.03  lits:                                   37
% 1.72/1.03  lits_eq:                                4
% 1.72/1.03  fd_pure:                                0
% 1.72/1.03  fd_pseudo:                              0
% 1.72/1.03  fd_cond:                                0
% 1.72/1.03  fd_pseudo_cond:                         1
% 1.72/1.03  ac_symbols:                             0
% 1.72/1.03  
% 1.72/1.03  ------ Propositional Solver
% 1.72/1.03  
% 1.72/1.03  prop_solver_calls:                      26
% 1.72/1.03  prop_fast_solver_calls:                 898
% 1.72/1.03  smt_solver_calls:                       0
% 1.72/1.03  smt_fast_solver_calls:                  0
% 1.72/1.03  prop_num_of_clauses:                    507
% 1.72/1.03  prop_preprocess_simplified:             2395
% 1.72/1.03  prop_fo_subsumed:                       38
% 1.72/1.03  prop_solver_time:                       0.
% 1.72/1.03  smt_solver_time:                        0.
% 1.72/1.03  smt_fast_solver_time:                   0.
% 1.72/1.03  prop_fast_solver_time:                  0.
% 1.72/1.03  prop_unsat_core_time:                   0.
% 1.72/1.03  
% 1.72/1.03  ------ QBF
% 1.72/1.03  
% 1.72/1.03  qbf_q_res:                              0
% 1.72/1.03  qbf_num_tautologies:                    0
% 1.72/1.03  qbf_prep_cycles:                        0
% 1.72/1.03  
% 1.72/1.03  ------ BMC1
% 1.72/1.03  
% 1.72/1.03  bmc1_current_bound:                     -1
% 1.72/1.03  bmc1_last_solved_bound:                 -1
% 1.72/1.03  bmc1_unsat_core_size:                   -1
% 1.72/1.03  bmc1_unsat_core_parents_size:           -1
% 1.72/1.03  bmc1_merge_next_fun:                    0
% 1.72/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.72/1.03  
% 1.72/1.03  ------ Instantiation
% 1.72/1.03  
% 1.72/1.03  inst_num_of_clauses:                    118
% 1.72/1.03  inst_num_in_passive:                    25
% 1.72/1.03  inst_num_in_active:                     72
% 1.72/1.03  inst_num_in_unprocessed:                20
% 1.72/1.03  inst_num_of_loops:                      78
% 1.72/1.03  inst_num_of_learning_restarts:          0
% 1.72/1.03  inst_num_moves_active_passive:          3
% 1.72/1.03  inst_lit_activity:                      0
% 1.72/1.03  inst_lit_activity_moves:                0
% 1.72/1.03  inst_num_tautologies:                   0
% 1.72/1.03  inst_num_prop_implied:                  0
% 1.72/1.03  inst_num_existing_simplified:           0
% 1.72/1.03  inst_num_eq_res_simplified:             0
% 1.72/1.03  inst_num_child_elim:                    0
% 1.72/1.03  inst_num_of_dismatching_blockings:      8
% 1.72/1.03  inst_num_of_non_proper_insts:           91
% 1.72/1.03  inst_num_of_duplicates:                 0
% 1.72/1.03  inst_inst_num_from_inst_to_res:         0
% 1.72/1.03  inst_dismatching_checking_time:         0.
% 1.72/1.03  
% 1.72/1.03  ------ Resolution
% 1.72/1.03  
% 1.72/1.03  res_num_of_clauses:                     0
% 1.72/1.03  res_num_in_passive:                     0
% 1.72/1.03  res_num_in_active:                      0
% 1.72/1.03  res_num_of_loops:                       93
% 1.72/1.03  res_forward_subset_subsumed:            22
% 1.72/1.03  res_backward_subset_subsumed:           0
% 1.72/1.03  res_forward_subsumed:                   0
% 1.72/1.03  res_backward_subsumed:                  0
% 1.72/1.03  res_forward_subsumption_resolution:     1
% 1.72/1.03  res_backward_subsumption_resolution:    2
% 1.72/1.03  res_clause_to_clause_subsumption:       77
% 1.72/1.03  res_orphan_elimination:                 0
% 1.72/1.03  res_tautology_del:                      29
% 1.72/1.03  res_num_eq_res_simplified:              2
% 1.72/1.03  res_num_sel_changes:                    0
% 1.72/1.03  res_moves_from_active_to_pass:          0
% 1.72/1.03  
% 1.72/1.03  ------ Superposition
% 1.72/1.03  
% 1.72/1.03  sup_time_total:                         0.
% 1.72/1.03  sup_time_generating:                    0.
% 1.72/1.03  sup_time_sim_full:                      0.
% 1.72/1.03  sup_time_sim_immed:                     0.
% 1.72/1.03  
% 1.72/1.03  sup_num_of_clauses:                     16
% 1.72/1.03  sup_num_in_active:                      13
% 1.72/1.03  sup_num_in_passive:                     3
% 1.72/1.03  sup_num_of_loops:                       14
% 1.72/1.03  sup_fw_superposition:                   1
% 1.72/1.03  sup_bw_superposition:                   2
% 1.72/1.03  sup_immediate_simplified:               0
% 1.72/1.03  sup_given_eliminated:                   0
% 1.72/1.03  comparisons_done:                       0
% 1.72/1.03  comparisons_avoided:                    0
% 1.72/1.03  
% 1.72/1.03  ------ Simplifications
% 1.72/1.03  
% 1.72/1.03  
% 1.72/1.03  sim_fw_subset_subsumed:                 0
% 1.72/1.03  sim_bw_subset_subsumed:                 2
% 1.72/1.03  sim_fw_subsumed:                        0
% 1.72/1.03  sim_bw_subsumed:                        0
% 1.72/1.03  sim_fw_subsumption_res:                 0
% 1.72/1.03  sim_bw_subsumption_res:                 0
% 1.72/1.03  sim_tautology_del:                      1
% 1.72/1.03  sim_eq_tautology_del:                   1
% 1.72/1.03  sim_eq_res_simp:                        0
% 1.72/1.03  sim_fw_demodulated:                     0
% 1.72/1.03  sim_bw_demodulated:                     0
% 1.72/1.03  sim_light_normalised:                   3
% 1.72/1.03  sim_joinable_taut:                      0
% 1.72/1.03  sim_joinable_simp:                      0
% 1.72/1.03  sim_ac_normalised:                      0
% 1.72/1.03  sim_smt_subsumption:                    0
% 1.72/1.03  
%------------------------------------------------------------------------------
