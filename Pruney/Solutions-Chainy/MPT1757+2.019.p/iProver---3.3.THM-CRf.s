%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:44 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :  209 (2234 expanded)
%              Number of clauses        :  125 ( 378 expanded)
%              Number of leaves         :   21 ( 882 expanded)
%              Depth                    :   32
%              Number of atoms          : 1483 (35888 expanded)
%              Number of equality atoms :  201 (2710 expanded)
%              Maximal formula depth    :   28 (   8 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f45,plain,(
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
    inference(flattening,[],[f45])).

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f53,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f46,f52,f51,f50,f49,f48,f47])).

fof(f85,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f88,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f53])).

fof(f90,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f53])).

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
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
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
    inference(flattening,[],[f35])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f98,plain,(
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
    inference(equality_resolution,[],[f72])).

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

fof(f71,plain,(
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

fof(f96,plain,(
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
    inference(equality_resolution,[],[f71])).

fof(f81,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f77,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f78,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f75,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f74,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f76,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f97,plain,(
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
    inference(equality_resolution,[],[f73])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f42,plain,(
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
    inference(flattening,[],[f42])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f84,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(cnf_transformation,[],[f19])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1011,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_1012,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1011])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1014,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1012,c_31])).

cnf(c_2600,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1014])).

cnf(c_21,negated_conjecture,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2604,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( sK4 = sK5 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2645,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2604,c_22])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2605,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2650,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2605,c_22])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_50,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f96])).

cnf(c_194,plain,
    ( ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_17])).

cnf(c_195,plain,
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
    inference(renaming,[status(thm)],[c_194])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_838,plain,
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
    inference(resolution_lifted,[status(thm)],[c_195,c_29])).

cnf(c_839,plain,
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
    inference(unflattening,[status(thm)],[c_838])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_843,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_839,c_30])).

cnf(c_844,plain,
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
    inference(renaming,[status(thm)],[c_843])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_879,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_844,c_7])).

cnf(c_1051,plain,
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
    inference(resolution_lifted,[status(thm)],[c_25,c_879])).

cnf(c_1052,plain,
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
    inference(unflattening,[status(thm)],[c_1051])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1056,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1052,c_33,c_32,c_31,c_27])).

cnf(c_1057,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1056])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1315,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1057,c_35])).

cnf(c_1316,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_1315])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1320,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ r1_tmap_1(sK1,sK0,sK2,X0)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1316,c_36,c_34,c_28])).

cnf(c_1321,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_1320])).

cnf(c_1707,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1321])).

cnf(c_2764,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_2765,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2764])).

cnf(c_2803,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2650,c_50,c_2765])).

cnf(c_2809,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2645,c_50,c_2650,c_2765])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_10,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_558,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X4)
    | X2 != X3
    | k1_tops_1(X1,X0) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_10])).

cnf(c_559,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(k1_tops_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_18,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_643,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X5,k1_tops_1(X6,X7))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X5,u1_struct_0(X6))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_tarski(X8,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X6)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(k1_tops_1(X6,X7))
    | X8 != X7
    | X0 != X6
    | X3 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_559,c_18])).

cnf(c_644,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,k1_tops_1(X0,X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(k1_tops_1(X0,X5)) ),
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_686,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,k1_tops_1(X0,X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(k1_tops_1(X0,X5)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_644,c_7])).

cnf(c_772,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,k1_tops_1(X0,X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(k1_tops_1(X0,X5))
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_686,c_29])).

cnf(c_773,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | r1_tmap_1(X2,X1,sK2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,k1_tops_1(X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v1_funct_1(sK2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(k1_tops_1(X2,X4))
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_772])).

cnf(c_777,plain,
    ( ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_tops_1(X2,X4))
    | ~ m1_pre_topc(X0,X2)
    | r1_tmap_1(X2,X1,sK2,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(k1_tops_1(X2,X4))
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_773,c_30])).

cnf(c_778,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | r1_tmap_1(X2,X1,sK2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,k1_tops_1(X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v1_xboole_0(k1_tops_1(X2,X4))
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_777])).

cnf(c_1090,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | r1_tmap_1(X2,X1,sK2,X3)
    | ~ m1_subset_1(X3,k1_tops_1(X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(k1_tops_1(X2,X4))
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK1 != X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_778])).

cnf(c_1091,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,k1_tops_1(sK1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK3))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | v1_xboole_0(k1_tops_1(sK1,X2))
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1090])).

cnf(c_1095,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,k1_tops_1(sK1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK3))
    | ~ v2_pre_topc(X0)
    | v1_xboole_0(k1_tops_1(sK1,X2))
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1091,c_33,c_32,c_31,c_27])).

cnf(c_1096,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,k1_tops_1(sK1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK3))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(k1_tops_1(sK1,X2))
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1095])).

cnf(c_1279,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,k1_tops_1(sK1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK3))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(k1_tops_1(sK1,X2))
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1096,c_35])).

cnf(c_1280,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,k1_tops_1(sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ r1_tarski(X1,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(k1_tops_1(sK1,X1))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_1279])).

cnf(c_1284,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_tops_1(sK1,X1))
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | r1_tmap_1(sK1,sK0,sK2,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK3))
    | v1_xboole_0(k1_tops_1(sK1,X1))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1280,c_36,c_34,c_28])).

cnf(c_1285,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,k1_tops_1(sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r1_tarski(X1,u1_struct_0(sK3))
    | v1_xboole_0(k1_tops_1(sK1,X1))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_1284])).

cnf(c_1711,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,k1_tops_1(sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r1_tarski(X1,u1_struct_0(sK3))
    | v1_xboole_0(k1_tops_1(sK1,X1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1285])).

cnf(c_2588,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) != iProver_top
    | m1_subset_1(X0,k1_tops_1(sK1,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k1_tops_1(sK1,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1711])).

cnf(c_2973,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK5,k1_tops_1(sK1,X0)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k1_tops_1(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2809,c_2588])).

cnf(c_3079,plain,
    ( m1_subset_1(sK5,k1_tops_1(sK1,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k1_tops_1(sK1,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2973,c_50,c_2650,c_2765])).

cnf(c_3080,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK5,k1_tops_1(sK1,X0)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k1_tops_1(sK1,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3079])).

cnf(c_3164,plain,
    ( m1_subset_1(sK5,k1_tops_1(sK1,u1_struct_0(sK3))) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k1_tops_1(sK1,u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2600,c_3080])).

cnf(c_42,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1013,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1012])).

cnf(c_9,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_15,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_202,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_16])).

cnf(c_203,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_202])).

cnf(c_26,negated_conjecture,
    ( v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_512,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_203,c_26])).

cnf(c_513,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_515,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_513,c_32,c_31,c_25])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X3,X2) = X2
    | u1_struct_0(sK3) != X2
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_515])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_531,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_527,c_31])).

cnf(c_532,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_531])).

cnf(c_1142,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1014,c_532])).

cnf(c_1339,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1142,c_32])).

cnf(c_1340,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1339])).

cnf(c_1344,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1340,c_31])).

cnf(c_2758,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1344])).

cnf(c_2767,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tarski(X0,u1_struct_0(sK3))
    | v1_xboole_0(k1_tops_1(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_1711])).

cnf(c_2825,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,k1_tops_1(sK1,u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
    | v1_xboole_0(k1_tops_1(sK1,u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_2767])).

cnf(c_2827,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK5,k1_tops_1(sK1,u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k1_tops_1(sK1,u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2825])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2826,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2829,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2826])).

cnf(c_2077,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2847,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2077])).

cnf(c_2081,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2782,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | X1 != u1_struct_0(sK3)
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2081])).

cnf(c_2846,plain,
    ( m1_subset_1(sK5,X0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | X0 != u1_struct_0(sK3)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2782])).

cnf(c_2985,plain,
    ( m1_subset_1(sK5,k1_tops_1(sK1,u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | k1_tops_1(sK1,u1_struct_0(sK3)) != u1_struct_0(sK3)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2846])).

cnf(c_2986,plain,
    ( k1_tops_1(sK1,u1_struct_0(sK3)) != u1_struct_0(sK3)
    | sK5 != sK5
    | m1_subset_1(sK5,k1_tops_1(sK1,u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2985])).

cnf(c_3473,plain,
    ( v1_xboole_0(k1_tops_1(sK1,u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3164,c_31,c_42,c_50,c_1012,c_1013,c_2650,c_2645,c_2758,c_2765,c_2827,c_2829,c_2847,c_2986])).

cnf(c_1357,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1142,c_35])).

cnf(c_1358,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1357])).

cnf(c_1362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1358,c_34])).

cnf(c_2593,plain,
    ( k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1362])).

cnf(c_3233,plain,
    ( k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2593,c_31,c_1012,c_2758])).

cnf(c_3477,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3473,c_3233])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_6,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_471,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_4,c_6])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1040,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_25])).

cnf(c_1041,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1040])).

cnf(c_1043,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1041,c_31])).

cnf(c_1433,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_471,c_1043])).

cnf(c_1434,plain,
    ( v2_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1433])).

cnf(c_1436,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1434,c_27])).

cnf(c_2590,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1436])).

cnf(c_3479,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3477,c_2590])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:26:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.88/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/0.98  
% 1.88/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.88/0.98  
% 1.88/0.98  ------  iProver source info
% 1.88/0.98  
% 1.88/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.88/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.88/0.98  git: non_committed_changes: false
% 1.88/0.98  git: last_make_outside_of_git: false
% 1.88/0.98  
% 1.88/0.98  ------ 
% 1.88/0.98  
% 1.88/0.98  ------ Input Options
% 1.88/0.98  
% 1.88/0.98  --out_options                           all
% 1.88/0.98  --tptp_safe_out                         true
% 1.88/0.98  --problem_path                          ""
% 1.88/0.98  --include_path                          ""
% 1.88/0.98  --clausifier                            res/vclausify_rel
% 1.88/0.98  --clausifier_options                    --mode clausify
% 1.88/0.98  --stdin                                 false
% 1.88/0.98  --stats_out                             all
% 1.88/0.98  
% 1.88/0.98  ------ General Options
% 1.88/0.98  
% 1.88/0.98  --fof                                   false
% 1.88/0.98  --time_out_real                         305.
% 1.88/0.98  --time_out_virtual                      -1.
% 1.88/0.98  --symbol_type_check                     false
% 1.88/0.98  --clausify_out                          false
% 1.88/0.98  --sig_cnt_out                           false
% 1.88/0.98  --trig_cnt_out                          false
% 1.88/0.98  --trig_cnt_out_tolerance                1.
% 1.88/0.98  --trig_cnt_out_sk_spl                   false
% 1.88/0.98  --abstr_cl_out                          false
% 1.88/0.98  
% 1.88/0.98  ------ Global Options
% 1.88/0.98  
% 1.88/0.98  --schedule                              default
% 1.88/0.98  --add_important_lit                     false
% 1.88/0.98  --prop_solver_per_cl                    1000
% 1.88/0.98  --min_unsat_core                        false
% 1.88/0.98  --soft_assumptions                      false
% 1.88/0.98  --soft_lemma_size                       3
% 1.88/0.98  --prop_impl_unit_size                   0
% 1.88/0.98  --prop_impl_unit                        []
% 1.88/0.98  --share_sel_clauses                     true
% 1.88/0.98  --reset_solvers                         false
% 1.88/0.98  --bc_imp_inh                            [conj_cone]
% 1.88/0.98  --conj_cone_tolerance                   3.
% 1.88/0.98  --extra_neg_conj                        none
% 1.88/0.98  --large_theory_mode                     true
% 1.88/0.98  --prolific_symb_bound                   200
% 1.88/0.98  --lt_threshold                          2000
% 1.88/0.98  --clause_weak_htbl                      true
% 1.88/0.98  --gc_record_bc_elim                     false
% 1.88/0.98  
% 1.88/0.98  ------ Preprocessing Options
% 1.88/0.98  
% 1.88/0.98  --preprocessing_flag                    true
% 1.88/0.98  --time_out_prep_mult                    0.1
% 1.88/0.98  --splitting_mode                        input
% 1.88/0.98  --splitting_grd                         true
% 1.88/0.98  --splitting_cvd                         false
% 1.88/0.98  --splitting_cvd_svl                     false
% 1.88/0.98  --splitting_nvd                         32
% 1.88/0.98  --sub_typing                            true
% 1.88/0.98  --prep_gs_sim                           true
% 1.88/0.98  --prep_unflatten                        true
% 1.88/0.98  --prep_res_sim                          true
% 1.88/0.98  --prep_upred                            true
% 1.88/0.98  --prep_sem_filter                       exhaustive
% 1.88/0.98  --prep_sem_filter_out                   false
% 1.88/0.98  --pred_elim                             true
% 1.88/0.98  --res_sim_input                         true
% 1.88/0.98  --eq_ax_congr_red                       true
% 1.88/0.98  --pure_diseq_elim                       true
% 1.88/0.98  --brand_transform                       false
% 1.88/0.98  --non_eq_to_eq                          false
% 1.88/0.98  --prep_def_merge                        true
% 1.88/0.98  --prep_def_merge_prop_impl              false
% 1.88/0.98  --prep_def_merge_mbd                    true
% 1.88/0.98  --prep_def_merge_tr_red                 false
% 1.88/0.98  --prep_def_merge_tr_cl                  false
% 1.88/0.98  --smt_preprocessing                     true
% 1.88/0.98  --smt_ac_axioms                         fast
% 1.88/0.98  --preprocessed_out                      false
% 1.88/0.98  --preprocessed_stats                    false
% 1.88/0.98  
% 1.88/0.98  ------ Abstraction refinement Options
% 1.88/0.98  
% 1.88/0.98  --abstr_ref                             []
% 1.88/0.98  --abstr_ref_prep                        false
% 1.88/0.98  --abstr_ref_until_sat                   false
% 1.88/0.98  --abstr_ref_sig_restrict                funpre
% 1.88/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.88/0.98  --abstr_ref_under                       []
% 1.88/0.98  
% 1.88/0.98  ------ SAT Options
% 1.88/0.98  
% 1.88/0.98  --sat_mode                              false
% 1.88/0.98  --sat_fm_restart_options                ""
% 1.88/0.98  --sat_gr_def                            false
% 1.88/0.98  --sat_epr_types                         true
% 1.88/0.98  --sat_non_cyclic_types                  false
% 1.88/0.98  --sat_finite_models                     false
% 1.88/0.98  --sat_fm_lemmas                         false
% 1.88/0.98  --sat_fm_prep                           false
% 1.88/0.98  --sat_fm_uc_incr                        true
% 1.88/0.98  --sat_out_model                         small
% 1.88/0.98  --sat_out_clauses                       false
% 1.88/0.98  
% 1.88/0.98  ------ QBF Options
% 1.88/0.98  
% 1.88/0.98  --qbf_mode                              false
% 1.88/0.98  --qbf_elim_univ                         false
% 1.88/0.98  --qbf_dom_inst                          none
% 1.88/0.98  --qbf_dom_pre_inst                      false
% 1.88/0.98  --qbf_sk_in                             false
% 1.88/0.98  --qbf_pred_elim                         true
% 1.88/0.98  --qbf_split                             512
% 1.88/0.98  
% 1.88/0.98  ------ BMC1 Options
% 1.88/0.98  
% 1.88/0.98  --bmc1_incremental                      false
% 1.88/0.98  --bmc1_axioms                           reachable_all
% 1.88/0.98  --bmc1_min_bound                        0
% 1.88/0.98  --bmc1_max_bound                        -1
% 1.88/0.98  --bmc1_max_bound_default                -1
% 1.88/0.98  --bmc1_symbol_reachability              true
% 1.88/0.98  --bmc1_property_lemmas                  false
% 1.88/0.98  --bmc1_k_induction                      false
% 1.88/0.98  --bmc1_non_equiv_states                 false
% 1.88/0.98  --bmc1_deadlock                         false
% 1.88/0.98  --bmc1_ucm                              false
% 1.88/0.98  --bmc1_add_unsat_core                   none
% 1.88/0.98  --bmc1_unsat_core_children              false
% 1.88/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.88/0.98  --bmc1_out_stat                         full
% 1.88/0.98  --bmc1_ground_init                      false
% 1.88/0.98  --bmc1_pre_inst_next_state              false
% 1.88/0.98  --bmc1_pre_inst_state                   false
% 1.88/0.98  --bmc1_pre_inst_reach_state             false
% 1.88/0.98  --bmc1_out_unsat_core                   false
% 1.88/0.98  --bmc1_aig_witness_out                  false
% 1.88/0.98  --bmc1_verbose                          false
% 1.88/0.98  --bmc1_dump_clauses_tptp                false
% 1.88/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.88/0.98  --bmc1_dump_file                        -
% 1.88/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.88/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.88/0.98  --bmc1_ucm_extend_mode                  1
% 1.88/0.98  --bmc1_ucm_init_mode                    2
% 1.88/0.98  --bmc1_ucm_cone_mode                    none
% 1.88/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.88/0.98  --bmc1_ucm_relax_model                  4
% 1.88/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.88/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.88/0.98  --bmc1_ucm_layered_model                none
% 1.88/0.98  --bmc1_ucm_max_lemma_size               10
% 1.88/0.98  
% 1.88/0.98  ------ AIG Options
% 1.88/0.98  
% 1.88/0.98  --aig_mode                              false
% 1.88/0.98  
% 1.88/0.98  ------ Instantiation Options
% 1.88/0.98  
% 1.88/0.98  --instantiation_flag                    true
% 1.88/0.98  --inst_sos_flag                         false
% 1.88/0.98  --inst_sos_phase                        true
% 1.88/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.88/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.88/0.98  --inst_lit_sel_side                     num_symb
% 1.88/0.98  --inst_solver_per_active                1400
% 1.88/0.98  --inst_solver_calls_frac                1.
% 1.88/0.98  --inst_passive_queue_type               priority_queues
% 1.88/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.88/0.98  --inst_passive_queues_freq              [25;2]
% 1.88/0.98  --inst_dismatching                      true
% 1.88/0.98  --inst_eager_unprocessed_to_passive     true
% 1.88/0.98  --inst_prop_sim_given                   true
% 1.88/0.98  --inst_prop_sim_new                     false
% 1.88/0.98  --inst_subs_new                         false
% 1.88/0.98  --inst_eq_res_simp                      false
% 1.88/0.98  --inst_subs_given                       false
% 1.88/0.98  --inst_orphan_elimination               true
% 1.88/0.98  --inst_learning_loop_flag               true
% 1.88/0.98  --inst_learning_start                   3000
% 1.88/0.98  --inst_learning_factor                  2
% 1.88/0.98  --inst_start_prop_sim_after_learn       3
% 1.88/0.98  --inst_sel_renew                        solver
% 1.88/0.98  --inst_lit_activity_flag                true
% 1.88/0.98  --inst_restr_to_given                   false
% 1.88/0.98  --inst_activity_threshold               500
% 1.88/0.98  --inst_out_proof                        true
% 1.88/0.98  
% 1.88/0.98  ------ Resolution Options
% 1.88/0.98  
% 1.88/0.98  --resolution_flag                       true
% 1.88/0.98  --res_lit_sel                           adaptive
% 1.88/0.98  --res_lit_sel_side                      none
% 1.88/0.98  --res_ordering                          kbo
% 1.88/0.98  --res_to_prop_solver                    active
% 1.88/0.98  --res_prop_simpl_new                    false
% 1.88/0.98  --res_prop_simpl_given                  true
% 1.88/0.98  --res_passive_queue_type                priority_queues
% 1.88/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.88/0.98  --res_passive_queues_freq               [15;5]
% 1.88/0.98  --res_forward_subs                      full
% 1.88/0.98  --res_backward_subs                     full
% 1.88/0.98  --res_forward_subs_resolution           true
% 1.88/0.98  --res_backward_subs_resolution          true
% 1.88/0.98  --res_orphan_elimination                true
% 1.88/0.98  --res_time_limit                        2.
% 1.88/0.98  --res_out_proof                         true
% 1.88/0.98  
% 1.88/0.98  ------ Superposition Options
% 1.88/0.98  
% 1.88/0.98  --superposition_flag                    true
% 1.88/0.98  --sup_passive_queue_type                priority_queues
% 1.88/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.88/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.88/0.98  --demod_completeness_check              fast
% 1.88/0.98  --demod_use_ground                      true
% 1.88/0.98  --sup_to_prop_solver                    passive
% 1.88/0.98  --sup_prop_simpl_new                    true
% 1.88/0.98  --sup_prop_simpl_given                  true
% 1.88/0.98  --sup_fun_splitting                     false
% 1.88/0.98  --sup_smt_interval                      50000
% 1.88/0.98  
% 1.88/0.98  ------ Superposition Simplification Setup
% 1.88/0.98  
% 1.88/0.98  --sup_indices_passive                   []
% 1.88/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.88/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.98  --sup_full_bw                           [BwDemod]
% 1.88/0.98  --sup_immed_triv                        [TrivRules]
% 1.88/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.88/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.98  --sup_immed_bw_main                     []
% 1.88/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.88/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/0.98  
% 1.88/0.98  ------ Combination Options
% 1.88/0.98  
% 1.88/0.98  --comb_res_mult                         3
% 1.88/0.98  --comb_sup_mult                         2
% 1.88/0.98  --comb_inst_mult                        10
% 1.88/0.98  
% 1.88/0.98  ------ Debug Options
% 1.88/0.98  
% 1.88/0.98  --dbg_backtrace                         false
% 1.88/0.98  --dbg_dump_prop_clauses                 false
% 1.88/0.98  --dbg_dump_prop_clauses_file            -
% 1.88/0.98  --dbg_out_stat                          false
% 1.88/0.98  ------ Parsing...
% 1.88/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.88/0.98  
% 1.88/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 1.88/0.98  
% 1.88/0.98  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.88/0.98  
% 1.88/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.88/0.98  ------ Proving...
% 1.88/0.98  ------ Problem Properties 
% 1.88/0.98  
% 1.88/0.98  
% 1.88/0.98  clauses                                 21
% 1.88/0.98  conjectures                             6
% 1.88/0.98  EPR                                     3
% 1.88/0.98  Horn                                    18
% 1.88/0.98  unary                                   9
% 1.88/0.98  binary                                  5
% 1.88/0.98  lits                                    50
% 1.88/0.98  lits eq                                 6
% 1.88/0.98  fd_pure                                 0
% 1.88/0.98  fd_pseudo                               0
% 1.88/0.98  fd_cond                                 0
% 1.88/0.98  fd_pseudo_cond                          1
% 1.88/0.98  AC symbols                              0
% 1.88/0.98  
% 1.88/0.98  ------ Schedule dynamic 5 is on 
% 1.88/0.98  
% 1.88/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.88/0.98  
% 1.88/0.98  
% 1.88/0.98  ------ 
% 1.88/0.98  Current options:
% 1.88/0.98  ------ 
% 1.88/0.98  
% 1.88/0.98  ------ Input Options
% 1.88/0.98  
% 1.88/0.98  --out_options                           all
% 1.88/0.98  --tptp_safe_out                         true
% 1.88/0.98  --problem_path                          ""
% 1.88/0.98  --include_path                          ""
% 1.88/0.98  --clausifier                            res/vclausify_rel
% 1.88/0.98  --clausifier_options                    --mode clausify
% 1.88/0.98  --stdin                                 false
% 1.88/0.98  --stats_out                             all
% 1.88/0.98  
% 1.88/0.98  ------ General Options
% 1.88/0.98  
% 1.88/0.98  --fof                                   false
% 1.88/0.98  --time_out_real                         305.
% 1.88/0.98  --time_out_virtual                      -1.
% 1.88/0.98  --symbol_type_check                     false
% 1.88/0.98  --clausify_out                          false
% 1.88/0.98  --sig_cnt_out                           false
% 1.88/0.98  --trig_cnt_out                          false
% 1.88/0.98  --trig_cnt_out_tolerance                1.
% 1.88/0.98  --trig_cnt_out_sk_spl                   false
% 1.88/0.98  --abstr_cl_out                          false
% 1.88/0.98  
% 1.88/0.98  ------ Global Options
% 1.88/0.98  
% 1.88/0.98  --schedule                              default
% 1.88/0.98  --add_important_lit                     false
% 1.88/0.98  --prop_solver_per_cl                    1000
% 1.88/0.98  --min_unsat_core                        false
% 1.88/0.98  --soft_assumptions                      false
% 1.88/0.98  --soft_lemma_size                       3
% 1.88/0.98  --prop_impl_unit_size                   0
% 1.88/0.98  --prop_impl_unit                        []
% 1.88/0.98  --share_sel_clauses                     true
% 1.88/0.98  --reset_solvers                         false
% 1.88/0.98  --bc_imp_inh                            [conj_cone]
% 1.88/0.98  --conj_cone_tolerance                   3.
% 1.88/0.98  --extra_neg_conj                        none
% 1.88/0.98  --large_theory_mode                     true
% 1.88/0.98  --prolific_symb_bound                   200
% 1.88/0.98  --lt_threshold                          2000
% 1.88/0.98  --clause_weak_htbl                      true
% 1.88/0.98  --gc_record_bc_elim                     false
% 1.88/0.98  
% 1.88/0.98  ------ Preprocessing Options
% 1.88/0.98  
% 1.88/0.98  --preprocessing_flag                    true
% 1.88/0.98  --time_out_prep_mult                    0.1
% 1.88/0.98  --splitting_mode                        input
% 1.88/0.98  --splitting_grd                         true
% 1.88/0.98  --splitting_cvd                         false
% 1.88/0.98  --splitting_cvd_svl                     false
% 1.88/0.98  --splitting_nvd                         32
% 1.88/0.98  --sub_typing                            true
% 1.88/0.98  --prep_gs_sim                           true
% 1.88/0.98  --prep_unflatten                        true
% 1.88/0.98  --prep_res_sim                          true
% 1.88/0.98  --prep_upred                            true
% 1.88/0.98  --prep_sem_filter                       exhaustive
% 1.88/0.98  --prep_sem_filter_out                   false
% 1.88/0.98  --pred_elim                             true
% 1.88/0.98  --res_sim_input                         true
% 1.88/0.98  --eq_ax_congr_red                       true
% 1.88/0.98  --pure_diseq_elim                       true
% 1.88/0.98  --brand_transform                       false
% 1.88/0.98  --non_eq_to_eq                          false
% 1.88/0.98  --prep_def_merge                        true
% 1.88/0.98  --prep_def_merge_prop_impl              false
% 1.88/0.98  --prep_def_merge_mbd                    true
% 1.88/0.98  --prep_def_merge_tr_red                 false
% 1.88/0.98  --prep_def_merge_tr_cl                  false
% 1.88/0.98  --smt_preprocessing                     true
% 1.88/0.98  --smt_ac_axioms                         fast
% 1.88/0.98  --preprocessed_out                      false
% 1.88/0.98  --preprocessed_stats                    false
% 1.88/0.98  
% 1.88/0.98  ------ Abstraction refinement Options
% 1.88/0.98  
% 1.88/0.98  --abstr_ref                             []
% 1.88/0.98  --abstr_ref_prep                        false
% 1.88/0.98  --abstr_ref_until_sat                   false
% 1.88/0.98  --abstr_ref_sig_restrict                funpre
% 1.88/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.88/0.98  --abstr_ref_under                       []
% 1.88/0.98  
% 1.88/0.98  ------ SAT Options
% 1.88/0.98  
% 1.88/0.98  --sat_mode                              false
% 1.88/0.98  --sat_fm_restart_options                ""
% 1.88/0.98  --sat_gr_def                            false
% 1.88/0.98  --sat_epr_types                         true
% 1.88/0.98  --sat_non_cyclic_types                  false
% 1.88/0.98  --sat_finite_models                     false
% 1.88/0.98  --sat_fm_lemmas                         false
% 1.88/0.98  --sat_fm_prep                           false
% 1.88/0.98  --sat_fm_uc_incr                        true
% 1.88/0.98  --sat_out_model                         small
% 1.88/0.98  --sat_out_clauses                       false
% 1.88/0.98  
% 1.88/0.98  ------ QBF Options
% 1.88/0.98  
% 1.88/0.98  --qbf_mode                              false
% 1.88/0.98  --qbf_elim_univ                         false
% 1.88/0.98  --qbf_dom_inst                          none
% 1.88/0.98  --qbf_dom_pre_inst                      false
% 1.88/0.98  --qbf_sk_in                             false
% 1.88/0.98  --qbf_pred_elim                         true
% 1.88/0.98  --qbf_split                             512
% 1.88/0.98  
% 1.88/0.98  ------ BMC1 Options
% 1.88/0.98  
% 1.88/0.98  --bmc1_incremental                      false
% 1.88/0.98  --bmc1_axioms                           reachable_all
% 1.88/0.98  --bmc1_min_bound                        0
% 1.88/0.98  --bmc1_max_bound                        -1
% 1.88/0.98  --bmc1_max_bound_default                -1
% 1.88/0.98  --bmc1_symbol_reachability              true
% 1.88/0.98  --bmc1_property_lemmas                  false
% 1.88/0.98  --bmc1_k_induction                      false
% 1.88/0.98  --bmc1_non_equiv_states                 false
% 1.88/0.98  --bmc1_deadlock                         false
% 1.88/0.98  --bmc1_ucm                              false
% 1.88/0.98  --bmc1_add_unsat_core                   none
% 1.88/0.98  --bmc1_unsat_core_children              false
% 1.88/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.88/0.98  --bmc1_out_stat                         full
% 1.88/0.98  --bmc1_ground_init                      false
% 1.88/0.98  --bmc1_pre_inst_next_state              false
% 1.88/0.98  --bmc1_pre_inst_state                   false
% 1.88/0.98  --bmc1_pre_inst_reach_state             false
% 1.88/0.98  --bmc1_out_unsat_core                   false
% 1.88/0.98  --bmc1_aig_witness_out                  false
% 1.88/0.98  --bmc1_verbose                          false
% 1.88/0.98  --bmc1_dump_clauses_tptp                false
% 1.88/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.88/0.98  --bmc1_dump_file                        -
% 1.88/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.88/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.88/0.98  --bmc1_ucm_extend_mode                  1
% 1.88/0.98  --bmc1_ucm_init_mode                    2
% 1.88/0.98  --bmc1_ucm_cone_mode                    none
% 1.88/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.88/0.98  --bmc1_ucm_relax_model                  4
% 1.88/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.88/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.88/0.98  --bmc1_ucm_layered_model                none
% 1.88/0.98  --bmc1_ucm_max_lemma_size               10
% 1.88/0.98  
% 1.88/0.98  ------ AIG Options
% 1.88/0.98  
% 1.88/0.98  --aig_mode                              false
% 1.88/0.98  
% 1.88/0.98  ------ Instantiation Options
% 1.88/0.98  
% 1.88/0.98  --instantiation_flag                    true
% 1.88/0.98  --inst_sos_flag                         false
% 1.88/0.98  --inst_sos_phase                        true
% 1.88/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.88/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.88/0.98  --inst_lit_sel_side                     none
% 1.88/0.98  --inst_solver_per_active                1400
% 1.88/0.98  --inst_solver_calls_frac                1.
% 1.88/0.98  --inst_passive_queue_type               priority_queues
% 1.88/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.88/0.98  --inst_passive_queues_freq              [25;2]
% 1.88/0.98  --inst_dismatching                      true
% 1.88/0.98  --inst_eager_unprocessed_to_passive     true
% 1.88/0.98  --inst_prop_sim_given                   true
% 1.88/0.98  --inst_prop_sim_new                     false
% 1.88/0.98  --inst_subs_new                         false
% 1.88/0.98  --inst_eq_res_simp                      false
% 1.88/0.98  --inst_subs_given                       false
% 1.88/0.98  --inst_orphan_elimination               true
% 1.88/0.98  --inst_learning_loop_flag               true
% 1.88/0.98  --inst_learning_start                   3000
% 1.88/0.98  --inst_learning_factor                  2
% 1.88/0.98  --inst_start_prop_sim_after_learn       3
% 1.88/0.98  --inst_sel_renew                        solver
% 1.88/0.98  --inst_lit_activity_flag                true
% 1.88/0.98  --inst_restr_to_given                   false
% 1.88/0.98  --inst_activity_threshold               500
% 1.88/0.98  --inst_out_proof                        true
% 1.88/0.98  
% 1.88/0.98  ------ Resolution Options
% 1.88/0.98  
% 1.88/0.98  --resolution_flag                       false
% 1.88/0.98  --res_lit_sel                           adaptive
% 1.88/0.98  --res_lit_sel_side                      none
% 1.88/0.98  --res_ordering                          kbo
% 1.88/0.98  --res_to_prop_solver                    active
% 1.88/0.98  --res_prop_simpl_new                    false
% 1.88/0.98  --res_prop_simpl_given                  true
% 1.88/0.98  --res_passive_queue_type                priority_queues
% 1.88/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.88/0.98  --res_passive_queues_freq               [15;5]
% 1.88/0.98  --res_forward_subs                      full
% 1.88/0.98  --res_backward_subs                     full
% 1.88/0.98  --res_forward_subs_resolution           true
% 1.88/0.98  --res_backward_subs_resolution          true
% 1.88/0.98  --res_orphan_elimination                true
% 1.88/0.98  --res_time_limit                        2.
% 1.88/0.98  --res_out_proof                         true
% 1.88/0.98  
% 1.88/0.98  ------ Superposition Options
% 1.88/0.98  
% 1.88/0.98  --superposition_flag                    true
% 1.88/0.98  --sup_passive_queue_type                priority_queues
% 1.88/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.88/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.88/0.98  --demod_completeness_check              fast
% 1.88/0.98  --demod_use_ground                      true
% 1.88/0.98  --sup_to_prop_solver                    passive
% 1.88/0.98  --sup_prop_simpl_new                    true
% 1.88/0.98  --sup_prop_simpl_given                  true
% 1.88/0.98  --sup_fun_splitting                     false
% 1.88/0.98  --sup_smt_interval                      50000
% 1.88/0.98  
% 1.88/0.98  ------ Superposition Simplification Setup
% 1.88/0.98  
% 1.88/0.98  --sup_indices_passive                   []
% 1.88/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.88/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.98  --sup_full_bw                           [BwDemod]
% 1.88/0.98  --sup_immed_triv                        [TrivRules]
% 1.88/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.88/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.98  --sup_immed_bw_main                     []
% 1.88/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.88/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/0.98  
% 1.88/0.98  ------ Combination Options
% 1.88/0.98  
% 1.88/0.98  --comb_res_mult                         3
% 1.88/0.98  --comb_sup_mult                         2
% 1.88/0.98  --comb_inst_mult                        10
% 1.88/0.98  
% 1.88/0.98  ------ Debug Options
% 1.88/0.98  
% 1.88/0.98  --dbg_backtrace                         false
% 1.88/0.98  --dbg_dump_prop_clauses                 false
% 1.88/0.98  --dbg_dump_prop_clauses_file            -
% 1.88/0.98  --dbg_out_stat                          false
% 1.88/0.98  
% 1.88/0.98  
% 1.88/0.98  
% 1.88/0.98  
% 1.88/0.98  ------ Proving...
% 1.88/0.98  
% 1.88/0.98  
% 1.88/0.98  % SZS status Theorem for theBenchmark.p
% 1.88/0.98  
% 1.88/0.98   Resolution empty clause
% 1.88/0.98  
% 1.88/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.88/0.98  
% 1.88/0.98  fof(f11,axiom,(
% 1.88/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/0.98  
% 1.88/0.98  fof(f32,plain,(
% 1.88/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.88/0.98    inference(ennf_transformation,[],[f11])).
% 1.88/0.98  
% 1.88/0.98  fof(f70,plain,(
% 1.88/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.88/0.98    inference(cnf_transformation,[],[f32])).
% 1.88/0.98  
% 1.88/0.98  fof(f14,conjecture,(
% 1.88/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/0.98  
% 1.88/0.98  fof(f15,negated_conjecture,(
% 1.88/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.88/0.98    inference(negated_conjecture,[],[f14])).
% 1.88/0.98  
% 1.88/0.98  fof(f37,plain,(
% 1.88/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.88/0.99    inference(ennf_transformation,[],[f15])).
% 1.88/0.99  
% 1.88/0.99  fof(f38,plain,(
% 1.88/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.88/0.99    inference(flattening,[],[f37])).
% 1.88/0.99  
% 1.88/0.99  fof(f45,plain,(
% 1.88/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.88/0.99    inference(nnf_transformation,[],[f38])).
% 1.88/0.99  
% 1.88/0.99  fof(f46,plain,(
% 1.88/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.88/0.99    inference(flattening,[],[f45])).
% 1.88/0.99  
% 1.88/0.99  fof(f52,plain,(
% 1.88/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK5) | r1_tmap_1(X1,X0,X2,X4)) & sK5 = X4 & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 1.88/0.99    introduced(choice_axiom,[])).
% 1.88/0.99  
% 1.88/0.99  fof(f51,plain,(
% 1.88/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK4)) & sK4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 1.88/0.99    introduced(choice_axiom,[])).
% 1.88/0.99  
% 1.88/0.99  fof(f50,plain,(
% 1.88/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK3,X1) & v1_tsep_1(sK3,X1) & ~v2_struct_0(sK3))) )),
% 1.88/0.99    introduced(choice_axiom,[])).
% 1.88/0.99  
% 1.88/0.99  fof(f49,plain,(
% 1.88/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X5) | ~r1_tmap_1(X1,X0,sK2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X5) | r1_tmap_1(X1,X0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK2))) )),
% 1.88/0.99    introduced(choice_axiom,[])).
% 1.88/0.99  
% 1.88/0.99  fof(f48,plain,(
% 1.88/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X5) | ~r1_tmap_1(sK1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X5) | r1_tmap_1(sK1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.88/0.99    introduced(choice_axiom,[])).
% 1.88/0.99  
% 1.88/0.99  fof(f47,plain,(
% 1.88/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | ~r1_tmap_1(X1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | r1_tmap_1(X1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.88/0.99    introduced(choice_axiom,[])).
% 1.88/0.99  
% 1.88/0.99  fof(f53,plain,(
% 1.88/0.99    ((((((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f46,f52,f51,f50,f49,f48,f47])).
% 1.88/0.99  
% 1.88/0.99  fof(f85,plain,(
% 1.88/0.99    m1_pre_topc(sK3,sK1)),
% 1.88/0.99    inference(cnf_transformation,[],[f53])).
% 1.88/0.99  
% 1.88/0.99  fof(f79,plain,(
% 1.88/0.99    l1_pre_topc(sK1)),
% 1.88/0.99    inference(cnf_transformation,[],[f53])).
% 1.88/0.99  
% 1.88/0.99  fof(f89,plain,(
% 1.88/0.99    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 1.88/0.99    inference(cnf_transformation,[],[f53])).
% 1.88/0.99  
% 1.88/0.99  fof(f88,plain,(
% 1.88/0.99    sK4 = sK5),
% 1.88/0.99    inference(cnf_transformation,[],[f53])).
% 1.88/0.99  
% 1.88/0.99  fof(f90,plain,(
% 1.88/0.99    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 1.88/0.99    inference(cnf_transformation,[],[f53])).
% 1.88/0.99  
% 1.88/0.99  fof(f87,plain,(
% 1.88/0.99    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.88/0.99    inference(cnf_transformation,[],[f53])).
% 1.88/0.99  
% 1.88/0.99  fof(f13,axiom,(
% 1.88/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/0.99  
% 1.88/0.99  fof(f35,plain,(
% 1.88/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.88/0.99    inference(ennf_transformation,[],[f13])).
% 1.88/0.99  
% 1.88/0.99  fof(f36,plain,(
% 1.88/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.88/0.99    inference(flattening,[],[f35])).
% 1.88/0.99  
% 1.88/0.99  fof(f44,plain,(
% 1.88/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.88/0.99    inference(nnf_transformation,[],[f36])).
% 1.88/0.99  
% 1.88/0.99  fof(f72,plain,(
% 1.88/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.88/0.99    inference(cnf_transformation,[],[f44])).
% 1.88/0.99  
% 1.88/0.99  fof(f98,plain,(
% 1.88/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.88/0.99    inference(equality_resolution,[],[f72])).
% 1.88/0.99  
% 1.88/0.99  fof(f12,axiom,(
% 1.88/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 1.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/0.99  
% 1.88/0.99  fof(f33,plain,(
% 1.88/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.88/0.99    inference(ennf_transformation,[],[f12])).
% 1.88/0.99  
% 1.88/0.99  fof(f34,plain,(
% 1.88/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.88/0.99    inference(flattening,[],[f33])).
% 1.88/0.99  
% 1.88/0.99  fof(f71,plain,(
% 1.88/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.88/0.99    inference(cnf_transformation,[],[f34])).
% 1.88/0.99  
% 1.88/0.99  fof(f96,plain,(
% 1.88/0.99    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.88/0.99    inference(equality_resolution,[],[f71])).
% 1.88/0.99  
% 1.88/0.99  fof(f81,plain,(
% 1.88/0.99    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.88/0.99    inference(cnf_transformation,[],[f53])).
% 1.88/0.99  
% 1.88/0.99  fof(f80,plain,(
% 1.88/0.99    v1_funct_1(sK2)),
% 1.88/0.99    inference(cnf_transformation,[],[f53])).
% 1.88/0.99  
% 1.88/0.99  fof(f6,axiom,(
% 1.88/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/0.99  
% 1.88/0.99  fof(f22,plain,(
% 1.88/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.88/0.99    inference(ennf_transformation,[],[f6])).
% 1.88/0.99  
% 1.88/0.99  fof(f23,plain,(
% 1.88/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.88/0.99    inference(flattening,[],[f22])).
% 1.88/0.99  
% 1.88/0.99  fof(f61,plain,(
% 1.88/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.88/0.99    inference(cnf_transformation,[],[f23])).
% 1.88/0.99  
% 1.88/0.99  fof(f77,plain,(
% 1.88/0.99    ~v2_struct_0(sK1)),
% 1.88/0.99    inference(cnf_transformation,[],[f53])).
% 1.88/0.99  
% 1.88/0.99  fof(f78,plain,(
% 1.88/0.99    v2_pre_topc(sK1)),
% 1.88/0.99    inference(cnf_transformation,[],[f53])).
% 1.88/0.99  
% 1.88/0.99  fof(f83,plain,(
% 1.88/0.99    ~v2_struct_0(sK3)),
% 1.88/0.99    inference(cnf_transformation,[],[f53])).
% 1.88/0.99  
% 1.88/0.99  fof(f75,plain,(
% 1.88/0.99    v2_pre_topc(sK0)),
% 1.88/0.99    inference(cnf_transformation,[],[f53])).
% 1.88/0.99  
% 1.88/0.99  fof(f74,plain,(
% 1.88/0.99    ~v2_struct_0(sK0)),
% 1.88/0.99    inference(cnf_transformation,[],[f53])).
% 1.88/0.99  
% 1.88/0.99  fof(f76,plain,(
% 1.88/0.99    l1_pre_topc(sK0)),
% 1.88/0.99    inference(cnf_transformation,[],[f53])).
% 1.88/0.99  
% 1.88/0.99  fof(f82,plain,(
% 1.88/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.88/0.99    inference(cnf_transformation,[],[f53])).
% 1.88/0.99  
% 1.88/0.99  fof(f2,axiom,(
% 1.88/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/0.99  
% 1.88/0.99  fof(f16,plain,(
% 1.88/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.88/0.99    inference(ennf_transformation,[],[f2])).
% 1.88/0.99  
% 1.88/0.99  fof(f17,plain,(
% 1.88/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.88/0.99    inference(flattening,[],[f16])).
% 1.88/0.99  
% 1.88/0.99  fof(f57,plain,(
% 1.88/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.88/0.99    inference(cnf_transformation,[],[f17])).
% 1.88/0.99  
% 1.88/0.99  fof(f8,axiom,(
% 1.88/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/0.99  
% 1.88/0.99  fof(f26,plain,(
% 1.88/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.88/0.99    inference(ennf_transformation,[],[f8])).
% 1.88/0.99  
% 1.88/0.99  fof(f27,plain,(
% 1.88/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.88/0.99    inference(flattening,[],[f26])).
% 1.88/0.99  
% 1.88/0.99  fof(f41,plain,(
% 1.88/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.88/0.99    inference(nnf_transformation,[],[f27])).
% 1.88/0.99  
% 1.88/0.99  fof(f65,plain,(
% 1.88/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.88/0.99    inference(cnf_transformation,[],[f41])).
% 1.88/0.99  
% 1.88/0.99  fof(f73,plain,(
% 1.88/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.88/0.99    inference(cnf_transformation,[],[f44])).
% 1.88/0.99  
% 1.88/0.99  fof(f97,plain,(
% 1.88/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.88/0.99    inference(equality_resolution,[],[f73])).
% 1.88/0.99  
% 1.88/0.99  fof(f7,axiom,(
% 1.88/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/0.99  
% 1.88/0.99  fof(f24,plain,(
% 1.88/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.88/0.99    inference(ennf_transformation,[],[f7])).
% 1.88/0.99  
% 1.88/0.99  fof(f25,plain,(
% 1.88/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.88/0.99    inference(flattening,[],[f24])).
% 1.88/0.99  
% 1.88/0.99  fof(f62,plain,(
% 1.88/0.99    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.88/0.99    inference(cnf_transformation,[],[f25])).
% 1.88/0.99  
% 1.88/0.99  fof(f10,axiom,(
% 1.88/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/0.99  
% 1.88/0.99  fof(f30,plain,(
% 1.88/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.88/0.99    inference(ennf_transformation,[],[f10])).
% 1.88/0.99  
% 1.88/0.99  fof(f31,plain,(
% 1.88/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.88/0.99    inference(flattening,[],[f30])).
% 1.88/0.99  
% 1.88/0.99  fof(f42,plain,(
% 1.88/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.88/0.99    inference(nnf_transformation,[],[f31])).
% 1.88/0.99  
% 1.88/0.99  fof(f43,plain,(
% 1.88/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.88/0.99    inference(flattening,[],[f42])).
% 1.88/0.99  
% 1.88/0.99  fof(f67,plain,(
% 1.88/0.99    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.88/0.99    inference(cnf_transformation,[],[f43])).
% 1.88/0.99  
% 1.88/0.99  fof(f95,plain,(
% 1.88/0.99    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.88/0.99    inference(equality_resolution,[],[f67])).
% 1.88/0.99  
% 1.88/0.99  fof(f84,plain,(
% 1.88/0.99    v1_tsep_1(sK3,sK1)),
% 1.88/0.99    inference(cnf_transformation,[],[f53])).
% 1.88/0.99  
% 1.88/0.99  fof(f1,axiom,(
% 1.88/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/0.99  
% 1.88/0.99  fof(f39,plain,(
% 1.88/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.88/0.99    inference(nnf_transformation,[],[f1])).
% 1.88/0.99  
% 1.88/0.99  fof(f40,plain,(
% 1.88/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.88/0.99    inference(flattening,[],[f39])).
% 1.88/0.99  
% 1.88/0.99  fof(f55,plain,(
% 1.88/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.88/0.99    inference(cnf_transformation,[],[f40])).
% 1.88/0.99  
% 1.88/0.99  fof(f91,plain,(
% 1.88/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.88/0.99    inference(equality_resolution,[],[f55])).
% 1.88/0.99  
% 1.88/0.99  fof(f3,axiom,(
% 1.88/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/0.99  
% 1.88/0.99  fof(f18,plain,(
% 1.88/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.88/0.99    inference(ennf_transformation,[],[f3])).
% 1.88/0.99  
% 1.88/0.99  fof(f58,plain,(
% 1.88/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.88/0.99    inference(cnf_transformation,[],[f18])).
% 1.88/0.99  
% 1.88/0.99  fof(f5,axiom,(
% 1.88/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/0.99  
% 1.88/0.99  fof(f20,plain,(
% 1.88/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.88/0.99    inference(ennf_transformation,[],[f5])).
% 1.88/0.99  
% 1.88/0.99  fof(f21,plain,(
% 1.88/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.88/0.99    inference(flattening,[],[f20])).
% 1.88/0.99  
% 1.88/0.99  fof(f60,plain,(
% 1.88/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.88/0.99    inference(cnf_transformation,[],[f21])).
% 1.88/0.99  
% 1.88/0.99  fof(f4,axiom,(
% 1.88/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/0.99  
% 1.88/0.99  fof(f19,plain,(
% 1.88/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.88/0.99    inference(ennf_transformation,[],[f4])).
% 1.88/0.99  
% 1.88/0.99  fof(f59,plain,(
% 1.88/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.88/0.99    inference(cnf_transformation,[],[f19])).
% 1.88/0.99  
% 1.88/0.99  cnf(c_16,plain,
% 1.88/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.88/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/0.99      | ~ l1_pre_topc(X1) ),
% 1.88/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_25,negated_conjecture,
% 1.88/0.99      ( m1_pre_topc(sK3,sK1) ),
% 1.88/0.99      inference(cnf_transformation,[],[f85]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1011,plain,
% 1.88/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | sK1 != X1
% 1.88/0.99      | sK3 != X0 ),
% 1.88/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1012,plain,
% 1.88/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/0.99      | ~ l1_pre_topc(sK1) ),
% 1.88/0.99      inference(unflattening,[status(thm)],[c_1011]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_31,negated_conjecture,
% 1.88/0.99      ( l1_pre_topc(sK1) ),
% 1.88/0.99      inference(cnf_transformation,[],[f79]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1014,plain,
% 1.88/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.88/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1012,c_31]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2600,plain,
% 1.88/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_1014]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_21,negated_conjecture,
% 1.88/0.99      ( r1_tmap_1(sK1,sK0,sK2,sK4)
% 1.88/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.88/0.99      inference(cnf_transformation,[],[f89]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2604,plain,
% 1.88/0.99      ( r1_tmap_1(sK1,sK0,sK2,sK4) = iProver_top
% 1.88/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_22,negated_conjecture,
% 1.88/0.99      ( sK4 = sK5 ),
% 1.88/0.99      inference(cnf_transformation,[],[f88]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2645,plain,
% 1.88/0.99      ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
% 1.88/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
% 1.88/0.99      inference(light_normalisation,[status(thm)],[c_2604,c_22]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_20,negated_conjecture,
% 1.88/0.99      ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
% 1.88/0.99      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.88/0.99      inference(cnf_transformation,[],[f90]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2605,plain,
% 1.88/0.99      ( r1_tmap_1(sK1,sK0,sK2,sK4) != iProver_top
% 1.88/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2650,plain,
% 1.88/0.99      ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
% 1.88/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
% 1.88/0.99      inference(light_normalisation,[status(thm)],[c_2605,c_22]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_23,negated_conjecture,
% 1.88/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 1.88/0.99      inference(cnf_transformation,[],[f87]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_50,plain,
% 1.88/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_19,plain,
% 1.88/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.88/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.88/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.88/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 1.88/0.99      | ~ m1_pre_topc(X4,X0)
% 1.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.88/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.88/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.88/0.99      | ~ v1_funct_1(X2)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | ~ v2_pre_topc(X0)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | v2_struct_0(X4)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | ~ l1_pre_topc(X0) ),
% 1.88/0.99      inference(cnf_transformation,[],[f98]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_17,plain,
% 1.88/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.88/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.88/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.88/0.99      | ~ m1_pre_topc(X4,X0)
% 1.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.88/0.99      | ~ v1_funct_1(X2)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | ~ v2_pre_topc(X0)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | v2_struct_0(X4)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | ~ l1_pre_topc(X0) ),
% 1.88/0.99      inference(cnf_transformation,[],[f96]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_194,plain,
% 1.88/0.99      ( ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.88/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.88/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.88/0.99      | ~ r1_tmap_1(X0,X1,X2,X3)
% 1.88/0.99      | ~ m1_pre_topc(X4,X0)
% 1.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.88/0.99      | ~ v1_funct_1(X2)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | ~ v2_pre_topc(X0)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | v2_struct_0(X4)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | ~ l1_pre_topc(X0) ),
% 1.88/0.99      inference(global_propositional_subsumption,[status(thm)],[c_19,c_17]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_195,plain,
% 1.88/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.88/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.88/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.88/0.99      | ~ m1_pre_topc(X4,X0)
% 1.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.88/0.99      | ~ v1_funct_1(X2)
% 1.88/0.99      | ~ v2_pre_topc(X0)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | v2_struct_0(X4)
% 1.88/0.99      | ~ l1_pre_topc(X0)
% 1.88/0.99      | ~ l1_pre_topc(X1) ),
% 1.88/0.99      inference(renaming,[status(thm)],[c_194]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_29,negated_conjecture,
% 1.88/0.99      ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 1.88/0.99      inference(cnf_transformation,[],[f81]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_838,plain,
% 1.88/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.88/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.88/0.99      | ~ m1_pre_topc(X4,X0)
% 1.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.88/0.99      | ~ v1_funct_1(X2)
% 1.88/0.99      | ~ v2_pre_topc(X0)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | v2_struct_0(X4)
% 1.88/0.99      | ~ l1_pre_topc(X0)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.88/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.88/0.99      | sK2 != X2 ),
% 1.88/0.99      inference(resolution_lifted,[status(thm)],[c_195,c_29]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_839,plain,
% 1.88/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.88/0.99      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.88/0.99      | ~ m1_pre_topc(X0,X2)
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.88/0.99      | ~ v1_funct_1(sK2)
% 1.88/0.99      | ~ v2_pre_topc(X2)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | v2_struct_0(X2)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | ~ l1_pre_topc(X2)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.88/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.88/0.99      inference(unflattening,[status(thm)],[c_838]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_30,negated_conjecture,
% 1.88/0.99      ( v1_funct_1(sK2) ),
% 1.88/0.99      inference(cnf_transformation,[],[f80]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_843,plain,
% 1.88/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.88/0.99      | ~ m1_pre_topc(X0,X2)
% 1.88/0.99      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.88/0.99      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.88/0.99      | ~ v2_pre_topc(X2)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | v2_struct_0(X2)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | ~ l1_pre_topc(X2)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.88/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.88/0.99      inference(global_propositional_subsumption,[status(thm)],[c_839,c_30]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_844,plain,
% 1.88/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.88/0.99      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.88/0.99      | ~ m1_pre_topc(X0,X2)
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | ~ v2_pre_topc(X2)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | v2_struct_0(X2)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | ~ l1_pre_topc(X2)
% 1.88/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.88/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.88/0.99      inference(renaming,[status(thm)],[c_843]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_7,plain,
% 1.88/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.88/0.99      | m1_subset_1(X2,u1_struct_0(X1))
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | ~ l1_pre_topc(X1) ),
% 1.88/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_879,plain,
% 1.88/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.88/0.99      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.88/0.99      | ~ m1_pre_topc(X0,X2)
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | ~ v2_pre_topc(X2)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | v2_struct_0(X2)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | ~ l1_pre_topc(X2)
% 1.88/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.88/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.88/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_844,c_7]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1051,plain,
% 1.88/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.88/0.99      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.88/0.99      | ~ v2_pre_topc(X2)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | v2_struct_0(X2)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | ~ l1_pre_topc(X2)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.88/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.88/0.99      | sK1 != X2
% 1.88/0.99      | sK3 != X0 ),
% 1.88/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_879]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1052,plain,
% 1.88/0.99      ( ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.88/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.88/0.99      | ~ v2_pre_topc(X0)
% 1.88/0.99      | ~ v2_pre_topc(sK1)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | v2_struct_0(sK1)
% 1.88/0.99      | v2_struct_0(sK3)
% 1.88/0.99      | ~ l1_pre_topc(X0)
% 1.88/0.99      | ~ l1_pre_topc(sK1)
% 1.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.88/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.88/0.99      inference(unflattening,[status(thm)],[c_1051]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_33,negated_conjecture,
% 1.88/0.99      ( ~ v2_struct_0(sK1) ),
% 1.88/0.99      inference(cnf_transformation,[],[f77]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_32,negated_conjecture,
% 1.88/0.99      ( v2_pre_topc(sK1) ),
% 1.88/0.99      inference(cnf_transformation,[],[f78]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_27,negated_conjecture,
% 1.88/0.99      ( ~ v2_struct_0(sK3) ),
% 1.88/0.99      inference(cnf_transformation,[],[f83]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1056,plain,
% 1.88/0.99      ( ~ l1_pre_topc(X0)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.88/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.88/0.99      | ~ v2_pre_topc(X0)
% 1.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.88/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.88/0.99      inference(global_propositional_subsumption,
% 1.88/0.99                [status(thm)],
% 1.88/0.99                [c_1052,c_33,c_32,c_31,c_27]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1057,plain,
% 1.88/0.99      ( ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.88/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.88/0.99      | ~ v2_pre_topc(X0)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | ~ l1_pre_topc(X0)
% 1.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.88/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.88/0.99      inference(renaming,[status(thm)],[c_1056]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_35,negated_conjecture,
% 1.88/0.99      ( v2_pre_topc(sK0) ),
% 1.88/0.99      inference(cnf_transformation,[],[f75]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1315,plain,
% 1.88/0.99      ( ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.88/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | ~ l1_pre_topc(X0)
% 1.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.88/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.88/0.99      | sK0 != X0 ),
% 1.88/0.99      inference(resolution_lifted,[status(thm)],[c_1057,c_35]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1316,plain,
% 1.88/0.99      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
% 1.88/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.88/0.99      | v2_struct_0(sK0)
% 1.88/0.99      | ~ l1_pre_topc(sK0)
% 1.88/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.88/0.99      inference(unflattening,[status(thm)],[c_1315]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_36,negated_conjecture,
% 1.88/0.99      ( ~ v2_struct_0(sK0) ),
% 1.88/0.99      inference(cnf_transformation,[],[f74]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_34,negated_conjecture,
% 1.88/0.99      ( l1_pre_topc(sK0) ),
% 1.88/0.99      inference(cnf_transformation,[],[f76]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_28,negated_conjecture,
% 1.88/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 1.88/0.99      inference(cnf_transformation,[],[f82]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1320,plain,
% 1.88/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.88/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.88/0.99      | ~ r1_tmap_1(sK1,sK0,sK2,X0)
% 1.88/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.88/0.99      inference(global_propositional_subsumption,
% 1.88/0.99                [status(thm)],
% 1.88/0.99                [c_1316,c_36,c_34,c_28]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1321,plain,
% 1.88/0.99      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
% 1.88/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.88/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.88/0.99      inference(renaming,[status(thm)],[c_1320]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1707,plain,
% 1.88/0.99      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
% 1.88/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.88/0.99      inference(equality_resolution_simp,[status(thm)],[c_1321]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2764,plain,
% 1.88/0.99      ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.88/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.88/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_1707]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2765,plain,
% 1.88/0.99      ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
% 1.88/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top
% 1.88/0.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_2764]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2803,plain,
% 1.88/0.99      ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top ),
% 1.88/0.99      inference(global_propositional_subsumption,
% 1.88/0.99                [status(thm)],
% 1.88/0.99                [c_2650,c_50,c_2765]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2809,plain,
% 1.88/0.99      ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
% 1.88/0.99      inference(global_propositional_subsumption,
% 1.88/0.99                [status(thm)],
% 1.88/0.99                [c_2645,c_50,c_2650,c_2765]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_3,plain,
% 1.88/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.88/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_10,plain,
% 1.88/0.99      ( m1_connsp_2(X0,X1,X2)
% 1.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.88/0.99      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | ~ l1_pre_topc(X1) ),
% 1.88/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_558,plain,
% 1.88/0.99      ( m1_connsp_2(X0,X1,X2)
% 1.88/0.99      | ~ m1_subset_1(X3,X4)
% 1.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | v1_xboole_0(X4)
% 1.88/0.99      | X2 != X3
% 1.88/0.99      | k1_tops_1(X1,X0) != X4 ),
% 1.88/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_10]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_559,plain,
% 1.88/0.99      ( m1_connsp_2(X0,X1,X2)
% 1.88/0.99      | ~ m1_subset_1(X2,k1_tops_1(X1,X0))
% 1.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | v1_xboole_0(k1_tops_1(X1,X0)) ),
% 1.88/0.99      inference(unflattening,[status(thm)],[c_558]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_18,plain,
% 1.88/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.88/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.88/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.88/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 1.88/0.99      | ~ m1_pre_topc(X4,X0)
% 1.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.88/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.88/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.88/0.99      | ~ v1_funct_1(X2)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | ~ v2_pre_topc(X0)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | v2_struct_0(X4)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | ~ l1_pre_topc(X0) ),
% 1.88/0.99      inference(cnf_transformation,[],[f97]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_643,plain,
% 1.88/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.88/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.88/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.88/0.99      | ~ m1_pre_topc(X4,X0)
% 1.88/0.99      | ~ m1_subset_1(X5,k1_tops_1(X6,X7))
% 1.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.88/0.99      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
% 1.88/0.99      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
% 1.88/0.99      | ~ m1_subset_1(X5,u1_struct_0(X6))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.88/0.99      | ~ r1_tarski(X8,u1_struct_0(X4))
% 1.88/0.99      | ~ v1_funct_1(X2)
% 1.88/0.99      | ~ v2_pre_topc(X6)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | ~ v2_pre_topc(X0)
% 1.88/0.99      | v2_struct_0(X6)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | v2_struct_0(X4)
% 1.88/0.99      | ~ l1_pre_topc(X6)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | ~ l1_pre_topc(X0)
% 1.88/0.99      | v1_xboole_0(k1_tops_1(X6,X7))
% 1.88/0.99      | X8 != X7
% 1.88/0.99      | X0 != X6
% 1.88/0.99      | X3 != X5 ),
% 1.88/0.99      inference(resolution_lifted,[status(thm)],[c_559,c_18]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_644,plain,
% 1.88/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.88/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.88/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.88/0.99      | ~ m1_pre_topc(X4,X0)
% 1.88/0.99      | ~ m1_subset_1(X3,k1_tops_1(X0,X5))
% 1.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.88/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.88/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.88/0.99      | ~ v1_funct_1(X2)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | ~ v2_pre_topc(X0)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | v2_struct_0(X4)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | ~ l1_pre_topc(X0)
% 1.88/0.99      | v1_xboole_0(k1_tops_1(X0,X5)) ),
% 1.88/0.99      inference(unflattening,[status(thm)],[c_643]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_686,plain,
% 1.88/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.88/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.88/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.88/0.99      | ~ m1_pre_topc(X4,X0)
% 1.88/0.99      | ~ m1_subset_1(X3,k1_tops_1(X0,X5))
% 1.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.88/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.88/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.88/0.99      | ~ v1_funct_1(X2)
% 1.88/0.99      | ~ v2_pre_topc(X0)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | v2_struct_0(X4)
% 1.88/0.99      | ~ l1_pre_topc(X0)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | v1_xboole_0(k1_tops_1(X0,X5)) ),
% 1.88/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_644,c_7]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_772,plain,
% 1.88/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.88/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.88/0.99      | ~ m1_pre_topc(X4,X0)
% 1.88/0.99      | ~ m1_subset_1(X3,k1_tops_1(X0,X5))
% 1.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.88/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.88/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.88/0.99      | ~ v1_funct_1(X2)
% 1.88/0.99      | ~ v2_pre_topc(X0)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | v2_struct_0(X4)
% 1.88/0.99      | ~ l1_pre_topc(X0)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | v1_xboole_0(k1_tops_1(X0,X5))
% 1.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.88/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.88/0.99      | sK2 != X2 ),
% 1.88/0.99      inference(resolution_lifted,[status(thm)],[c_686,c_29]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_773,plain,
% 1.88/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.88/0.99      | r1_tmap_1(X2,X1,sK2,X3)
% 1.88/0.99      | ~ m1_pre_topc(X0,X2)
% 1.88/0.99      | ~ m1_subset_1(X3,k1_tops_1(X2,X4))
% 1.88/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.88/0.99      | ~ r1_tarski(X4,u1_struct_0(X0))
% 1.88/0.99      | ~ v1_funct_1(sK2)
% 1.88/0.99      | ~ v2_pre_topc(X2)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | v2_struct_0(X2)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | ~ l1_pre_topc(X2)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | v1_xboole_0(k1_tops_1(X2,X4))
% 1.88/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.88/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.88/0.99      inference(unflattening,[status(thm)],[c_772]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_777,plain,
% 1.88/0.99      ( ~ r1_tarski(X4,u1_struct_0(X0))
% 1.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.88/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 1.88/0.99      | ~ m1_subset_1(X3,k1_tops_1(X2,X4))
% 1.88/0.99      | ~ m1_pre_topc(X0,X2)
% 1.88/0.99      | r1_tmap_1(X2,X1,sK2,X3)
% 1.88/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.88/0.99      | ~ v2_pre_topc(X2)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | v2_struct_0(X2)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | ~ l1_pre_topc(X2)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | v1_xboole_0(k1_tops_1(X2,X4))
% 1.88/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.88/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.88/0.99      inference(global_propositional_subsumption,[status(thm)],[c_773,c_30]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_778,plain,
% 1.88/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.88/0.99      | r1_tmap_1(X2,X1,sK2,X3)
% 1.88/0.99      | ~ m1_pre_topc(X0,X2)
% 1.88/0.99      | ~ m1_subset_1(X3,k1_tops_1(X2,X4))
% 1.88/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.88/0.99      | ~ r1_tarski(X4,u1_struct_0(X0))
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | ~ v2_pre_topc(X2)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | v2_struct_0(X2)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | ~ l1_pre_topc(X2)
% 1.88/0.99      | v1_xboole_0(k1_tops_1(X2,X4))
% 1.88/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.88/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.88/0.99      inference(renaming,[status(thm)],[c_777]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1090,plain,
% 1.88/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.88/0.99      | r1_tmap_1(X2,X1,sK2,X3)
% 1.88/0.99      | ~ m1_subset_1(X3,k1_tops_1(X2,X4))
% 1.88/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 1.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.88/0.99      | ~ r1_tarski(X4,u1_struct_0(X0))
% 1.88/0.99      | ~ v2_pre_topc(X2)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | v2_struct_0(X2)
% 1.88/0.99      | v2_struct_0(X1)
% 1.88/0.99      | ~ l1_pre_topc(X2)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | v1_xboole_0(k1_tops_1(X2,X4))
% 1.88/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.88/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.88/0.99      | sK1 != X2
% 1.88/0.99      | sK3 != X0 ),
% 1.88/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_778]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1091,plain,
% 1.88/0.99      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.88/0.99      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.88/0.99      | ~ m1_subset_1(X1,k1_tops_1(sK1,X2))
% 1.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.88/0.99      | ~ r1_tarski(X2,u1_struct_0(sK3))
% 1.88/0.99      | ~ v2_pre_topc(X0)
% 1.88/0.99      | ~ v2_pre_topc(sK1)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | v2_struct_0(sK1)
% 1.88/0.99      | v2_struct_0(sK3)
% 1.88/0.99      | ~ l1_pre_topc(X0)
% 1.88/0.99      | ~ l1_pre_topc(sK1)
% 1.88/0.99      | v1_xboole_0(k1_tops_1(sK1,X2))
% 1.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.88/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.88/0.99      inference(unflattening,[status(thm)],[c_1090]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1095,plain,
% 1.88/0.99      ( ~ l1_pre_topc(X0)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | r1_tmap_1(sK1,X0,sK2,X1)
% 1.88/0.99      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.88/0.99      | ~ m1_subset_1(X1,k1_tops_1(sK1,X2))
% 1.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.88/0.99      | ~ r1_tarski(X2,u1_struct_0(sK3))
% 1.88/0.99      | ~ v2_pre_topc(X0)
% 1.88/0.99      | v1_xboole_0(k1_tops_1(sK1,X2))
% 1.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.88/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.88/0.99      inference(global_propositional_subsumption,
% 1.88/0.99                [status(thm)],
% 1.88/0.99                [c_1091,c_33,c_32,c_31,c_27]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1096,plain,
% 1.88/0.99      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.88/0.99      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.88/0.99      | ~ m1_subset_1(X1,k1_tops_1(sK1,X2))
% 1.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.88/0.99      | ~ r1_tarski(X2,u1_struct_0(sK3))
% 1.88/0.99      | ~ v2_pre_topc(X0)
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | ~ l1_pre_topc(X0)
% 1.88/0.99      | v1_xboole_0(k1_tops_1(sK1,X2))
% 1.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.88/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.88/0.99      inference(renaming,[status(thm)],[c_1095]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1279,plain,
% 1.88/0.99      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.88/0.99      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.88/0.99      | ~ m1_subset_1(X1,k1_tops_1(sK1,X2))
% 1.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.88/0.99      | ~ r1_tarski(X2,u1_struct_0(sK3))
% 1.88/0.99      | v2_struct_0(X0)
% 1.88/0.99      | ~ l1_pre_topc(X0)
% 1.88/0.99      | v1_xboole_0(k1_tops_1(sK1,X2))
% 1.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.88/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.88/0.99      | sK0 != X0 ),
% 1.88/0.99      inference(resolution_lifted,[status(thm)],[c_1096,c_35]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1280,plain,
% 1.88/0.99      ( r1_tmap_1(sK1,sK0,sK2,X0)
% 1.88/0.99      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.88/0.99      | ~ m1_subset_1(X0,k1_tops_1(sK1,X1))
% 1.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.88/0.99      | ~ r1_tarski(X1,u1_struct_0(sK3))
% 1.88/0.99      | v2_struct_0(sK0)
% 1.88/0.99      | ~ l1_pre_topc(sK0)
% 1.88/0.99      | v1_xboole_0(k1_tops_1(sK1,X1))
% 1.88/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.88/0.99      inference(unflattening,[status(thm)],[c_1279]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1284,plain,
% 1.88/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/0.99      | ~ m1_subset_1(X0,k1_tops_1(sK1,X1))
% 1.88/0.99      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.88/0.99      | r1_tmap_1(sK1,sK0,sK2,X0)
% 1.88/0.99      | ~ r1_tarski(X1,u1_struct_0(sK3))
% 1.88/0.99      | v1_xboole_0(k1_tops_1(sK1,X1))
% 1.88/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.88/0.99      inference(global_propositional_subsumption,
% 1.88/0.99                [status(thm)],
% 1.88/0.99                [c_1280,c_36,c_34,c_28]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1285,plain,
% 1.88/0.99      ( r1_tmap_1(sK1,sK0,sK2,X0)
% 1.88/0.99      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.88/0.99      | ~ m1_subset_1(X0,k1_tops_1(sK1,X1))
% 1.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.88/0.99      | ~ r1_tarski(X1,u1_struct_0(sK3))
% 1.88/0.99      | v1_xboole_0(k1_tops_1(sK1,X1))
% 1.88/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.88/0.99      inference(renaming,[status(thm)],[c_1284]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1711,plain,
% 1.88/0.99      ( r1_tmap_1(sK1,sK0,sK2,X0)
% 1.88/0.99      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.88/0.99      | ~ m1_subset_1(X0,k1_tops_1(sK1,X1))
% 1.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.88/0.99      | ~ r1_tarski(X1,u1_struct_0(sK3))
% 1.88/0.99      | v1_xboole_0(k1_tops_1(sK1,X1)) ),
% 1.88/0.99      inference(equality_resolution_simp,[status(thm)],[c_1285]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2588,plain,
% 1.88/0.99      ( r1_tmap_1(sK1,sK0,sK2,X0) = iProver_top
% 1.88/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) != iProver_top
% 1.88/0.99      | m1_subset_1(X0,k1_tops_1(sK1,X1)) != iProver_top
% 1.88/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.88/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 1.88/0.99      | r1_tarski(X1,u1_struct_0(sK3)) != iProver_top
% 1.88/0.99      | v1_xboole_0(k1_tops_1(sK1,X1)) = iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_1711]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2973,plain,
% 1.88/0.99      ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
% 1.88/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.88/0.99      | m1_subset_1(sK5,k1_tops_1(sK1,X0)) != iProver_top
% 1.88/0.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 1.88/0.99      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 1.88/0.99      | v1_xboole_0(k1_tops_1(sK1,X0)) = iProver_top ),
% 1.88/0.99      inference(superposition,[status(thm)],[c_2809,c_2588]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_3079,plain,
% 1.88/0.99      ( m1_subset_1(sK5,k1_tops_1(sK1,X0)) != iProver_top
% 1.88/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.88/0.99      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 1.88/0.99      | v1_xboole_0(k1_tops_1(sK1,X0)) = iProver_top ),
% 1.88/0.99      inference(global_propositional_subsumption,
% 1.88/0.99                [status(thm)],
% 1.88/0.99                [c_2973,c_50,c_2650,c_2765]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_3080,plain,
% 1.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.88/0.99      | m1_subset_1(sK5,k1_tops_1(sK1,X0)) != iProver_top
% 1.88/0.99      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 1.88/0.99      | v1_xboole_0(k1_tops_1(sK1,X0)) = iProver_top ),
% 1.88/0.99      inference(renaming,[status(thm)],[c_3079]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_3164,plain,
% 1.88/0.99      ( m1_subset_1(sK5,k1_tops_1(sK1,u1_struct_0(sK3))) != iProver_top
% 1.88/0.99      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 1.88/0.99      | v1_xboole_0(k1_tops_1(sK1,u1_struct_0(sK3))) = iProver_top ),
% 1.88/0.99      inference(superposition,[status(thm)],[c_2600,c_3080]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_42,plain,
% 1.88/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1013,plain,
% 1.88/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.88/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_1012]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_9,plain,
% 1.88/0.99      ( ~ v3_pre_topc(X0,X1)
% 1.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.88/0.99      | ~ v2_pre_topc(X3)
% 1.88/0.99      | ~ l1_pre_topc(X3)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | k1_tops_1(X1,X0) = X0 ),
% 1.88/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_15,plain,
% 1.88/0.99      ( ~ v1_tsep_1(X0,X1)
% 1.88/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.88/0.99      | ~ m1_pre_topc(X0,X1)
% 1.88/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | ~ l1_pre_topc(X1) ),
% 1.88/0.99      inference(cnf_transformation,[],[f95]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_202,plain,
% 1.88/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.88/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.88/0.99      | ~ v1_tsep_1(X0,X1)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | ~ l1_pre_topc(X1) ),
% 1.88/0.99      inference(global_propositional_subsumption,[status(thm)],[c_15,c_16]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_203,plain,
% 1.88/0.99      ( ~ v1_tsep_1(X0,X1)
% 1.88/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.88/0.99      | ~ m1_pre_topc(X0,X1)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | ~ l1_pre_topc(X1) ),
% 1.88/0.99      inference(renaming,[status(thm)],[c_202]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_26,negated_conjecture,
% 1.88/0.99      ( v1_tsep_1(sK3,sK1) ),
% 1.88/0.99      inference(cnf_transformation,[],[f84]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_512,plain,
% 1.88/0.99      ( v3_pre_topc(u1_struct_0(X0),X1)
% 1.88/0.99      | ~ m1_pre_topc(X0,X1)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | sK1 != X1
% 1.88/0.99      | sK3 != X0 ),
% 1.88/0.99      inference(resolution_lifted,[status(thm)],[c_203,c_26]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_513,plain,
% 1.88/0.99      ( v3_pre_topc(u1_struct_0(sK3),sK1)
% 1.88/0.99      | ~ m1_pre_topc(sK3,sK1)
% 1.88/0.99      | ~ v2_pre_topc(sK1)
% 1.88/0.99      | ~ l1_pre_topc(sK1) ),
% 1.88/0.99      inference(unflattening,[status(thm)],[c_512]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_515,plain,
% 1.88/0.99      ( v3_pre_topc(u1_struct_0(sK3),sK1) ),
% 1.88/0.99      inference(global_propositional_subsumption,
% 1.88/0.99                [status(thm)],
% 1.88/0.99                [c_513,c_32,c_31,c_25]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_526,plain,
% 1.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | ~ l1_pre_topc(X3)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | k1_tops_1(X3,X2) = X2
% 1.88/0.99      | u1_struct_0(sK3) != X2
% 1.88/0.99      | sK1 != X3 ),
% 1.88/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_515]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_527,plain,
% 1.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | ~ l1_pre_topc(sK1)
% 1.88/0.99      | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 1.88/0.99      inference(unflattening,[status(thm)],[c_526]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_531,plain,
% 1.88/0.99      ( ~ l1_pre_topc(X1)
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/0.99      | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 1.88/0.99      inference(global_propositional_subsumption,[status(thm)],[c_527,c_31]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_532,plain,
% 1.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 1.88/0.99      inference(renaming,[status(thm)],[c_531]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1142,plain,
% 1.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/0.99      | ~ v2_pre_topc(X1)
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 1.88/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_1014,c_532]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1339,plain,
% 1.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3)
% 1.88/0.99      | sK1 != X1 ),
% 1.88/0.99      inference(resolution_lifted,[status(thm)],[c_1142,c_32]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1340,plain,
% 1.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/0.99      | ~ l1_pre_topc(sK1)
% 1.88/0.99      | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 1.88/0.99      inference(unflattening,[status(thm)],[c_1339]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1344,plain,
% 1.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/0.99      | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 1.88/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1340,c_31]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2758,plain,
% 1.88/0.99      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/0.99      | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_1344]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2767,plain,
% 1.88/0.99      ( r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.88/0.99      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/0.99      | ~ m1_subset_1(sK5,k1_tops_1(sK1,X0))
% 1.88/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.88/0.99      | ~ r1_tarski(X0,u1_struct_0(sK3))
% 1.88/0.99      | v1_xboole_0(k1_tops_1(sK1,X0)) ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_1711]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2825,plain,
% 1.88/0.99      ( r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.88/0.99      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.88/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/0.99      | ~ m1_subset_1(sK5,k1_tops_1(sK1,u1_struct_0(sK3)))
% 1.88/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.88/0.99      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
% 1.88/0.99      | v1_xboole_0(k1_tops_1(sK1,u1_struct_0(sK3))) ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_2767]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2827,plain,
% 1.88/0.99      ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
% 1.88/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top
% 1.88/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.88/0.99      | m1_subset_1(sK5,k1_tops_1(sK1,u1_struct_0(sK3))) != iProver_top
% 1.88/0.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 1.88/0.99      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 1.88/0.99      | v1_xboole_0(k1_tops_1(sK1,u1_struct_0(sK3))) = iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_2825]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f91]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2826,plain,
% 1.88/0.99      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2829,plain,
% 1.88/0.99      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_2826]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2077,plain,( X0 = X0 ),theory(equality) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2847,plain,
% 1.88/0.99      ( sK5 = sK5 ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_2077]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2081,plain,
% 1.88/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.88/0.99      theory(equality) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2782,plain,
% 1.88/0.99      ( m1_subset_1(X0,X1)
% 1.88/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.88/0.99      | X1 != u1_struct_0(sK3)
% 1.88/0.99      | X0 != sK5 ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_2081]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2846,plain,
% 1.88/0.99      ( m1_subset_1(sK5,X0)
% 1.88/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.88/0.99      | X0 != u1_struct_0(sK3)
% 1.88/0.99      | sK5 != sK5 ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_2782]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2985,plain,
% 1.88/0.99      ( m1_subset_1(sK5,k1_tops_1(sK1,u1_struct_0(sK3)))
% 1.88/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.88/0.99      | k1_tops_1(sK1,u1_struct_0(sK3)) != u1_struct_0(sK3)
% 1.88/0.99      | sK5 != sK5 ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_2846]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2986,plain,
% 1.88/0.99      ( k1_tops_1(sK1,u1_struct_0(sK3)) != u1_struct_0(sK3)
% 1.88/0.99      | sK5 != sK5
% 1.88/0.99      | m1_subset_1(sK5,k1_tops_1(sK1,u1_struct_0(sK3))) = iProver_top
% 1.88/0.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_2985]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_3473,plain,
% 1.88/0.99      ( v1_xboole_0(k1_tops_1(sK1,u1_struct_0(sK3))) = iProver_top ),
% 1.88/0.99      inference(global_propositional_subsumption,
% 1.88/0.99                [status(thm)],
% 1.88/0.99                [c_3164,c_31,c_42,c_50,c_1012,c_1013,c_2650,c_2645,c_2758,
% 1.88/0.99                 c_2765,c_2827,c_2829,c_2847,c_2986]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1357,plain,
% 1.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/0.99      | ~ l1_pre_topc(X1)
% 1.88/0.99      | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3)
% 1.88/0.99      | sK0 != X1 ),
% 1.88/0.99      inference(resolution_lifted,[status(thm)],[c_1142,c_35]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1358,plain,
% 1.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.88/0.99      | ~ l1_pre_topc(sK0)
% 1.88/0.99      | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 1.88/0.99      inference(unflattening,[status(thm)],[c_1357]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1362,plain,
% 1.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.88/0.99      | k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 1.88/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1358,c_34]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2593,plain,
% 1.88/0.99      ( k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3)
% 1.88/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_1362]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_3233,plain,
% 1.88/0.99      ( k1_tops_1(sK1,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 1.88/0.99      inference(global_propositional_subsumption,
% 1.88/0.99                [status(thm)],
% 1.88/0.99                [c_2593,c_31,c_1012,c_2758]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_3477,plain,
% 1.88/0.99      ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.88/0.99      inference(light_normalisation,[status(thm)],[c_3473,c_3233]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_4,plain,
% 1.88/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.88/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_6,plain,
% 1.88/0.99      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.88/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_471,plain,
% 1.88/0.99      ( v2_struct_0(X0) | ~ l1_pre_topc(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.88/0.99      inference(resolution,[status(thm)],[c_4,c_6]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_5,plain,
% 1.88/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.88/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1040,plain,
% 1.88/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK1 != X0 | sK3 != X1 ),
% 1.88/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_25]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1041,plain,
% 1.88/0.99      ( ~ l1_pre_topc(sK1) | l1_pre_topc(sK3) ),
% 1.88/0.99      inference(unflattening,[status(thm)],[c_1040]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1043,plain,
% 1.88/0.99      ( l1_pre_topc(sK3) ),
% 1.88/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1041,c_31]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1433,plain,
% 1.88/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 1.88/0.99      inference(resolution_lifted,[status(thm)],[c_471,c_1043]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1434,plain,
% 1.88/0.99      ( v2_struct_0(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.88/0.99      inference(unflattening,[status(thm)],[c_1433]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1436,plain,
% 1.88/0.99      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.88/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1434,c_27]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2590,plain,
% 1.88/0.99      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_1436]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_3479,plain,
% 1.88/0.99      ( $false ),
% 1.88/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3477,c_2590]) ).
% 1.88/0.99  
% 1.88/0.99  
% 1.88/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.88/0.99  
% 1.88/0.99  ------                               Statistics
% 1.88/0.99  
% 1.88/0.99  ------ General
% 1.88/0.99  
% 1.88/0.99  abstr_ref_over_cycles:                  0
% 1.88/0.99  abstr_ref_under_cycles:                 0
% 1.88/0.99  gc_basic_clause_elim:                   0
% 1.88/0.99  forced_gc_time:                         0
% 1.88/0.99  parsing_time:                           0.011
% 1.88/0.99  unif_index_cands_time:                  0.
% 1.88/0.99  unif_index_add_time:                    0.
% 1.88/0.99  orderings_time:                         0.
% 1.88/0.99  out_proof_time:                         0.014
% 1.88/0.99  total_time:                             0.14
% 1.88/0.99  num_of_symbols:                         59
% 1.88/0.99  num_of_terms:                           1922
% 1.88/0.99  
% 1.88/0.99  ------ Preprocessing
% 1.88/0.99  
% 1.88/0.99  num_of_splits:                          2
% 1.88/0.99  num_of_split_atoms:                     2
% 1.88/0.99  num_of_reused_defs:                     0
% 1.88/0.99  num_eq_ax_congr_red:                    11
% 1.88/0.99  num_of_sem_filtered_clauses:            1
% 1.88/0.99  num_of_subtypes:                        0
% 1.88/0.99  monotx_restored_types:                  0
% 1.88/0.99  sat_num_of_epr_types:                   0
% 1.88/0.99  sat_num_of_non_cyclic_types:            0
% 1.88/0.99  sat_guarded_non_collapsed_types:        0
% 1.88/0.99  num_pure_diseq_elim:                    0
% 1.88/0.99  simp_replaced_by:                       0
% 1.88/0.99  res_preprocessed:                       119
% 1.88/0.99  prep_upred:                             0
% 1.88/0.99  prep_unflattend:                        32
% 1.88/0.99  smt_new_axioms:                         0
% 1.88/0.99  pred_elim_cands:                        4
% 1.88/0.99  pred_elim:                              11
% 1.88/0.99  pred_elim_cl:                           16
% 1.88/0.99  pred_elim_cycles:                       18
% 1.88/0.99  merged_defs:                            8
% 1.88/0.99  merged_defs_ncl:                        0
% 1.88/0.99  bin_hyper_res:                          8
% 1.88/0.99  prep_cycles:                            4
% 1.88/0.99  pred_elim_time:                         0.04
% 1.88/0.99  splitting_time:                         0.
% 1.88/0.99  sem_filter_time:                        0.
% 1.88/0.99  monotx_time:                            0.
% 1.88/0.99  subtype_inf_time:                       0.
% 1.88/0.99  
% 1.88/0.99  ------ Problem properties
% 1.88/0.99  
% 1.88/0.99  clauses:                                21
% 1.88/0.99  conjectures:                            6
% 1.88/0.99  epr:                                    3
% 1.88/0.99  horn:                                   18
% 1.88/0.99  ground:                                 12
% 1.88/0.99  unary:                                  9
% 1.88/0.99  binary:                                 5
% 1.88/0.99  lits:                                   50
% 1.88/0.99  lits_eq:                                6
% 1.88/0.99  fd_pure:                                0
% 1.88/0.99  fd_pseudo:                              0
% 1.88/0.99  fd_cond:                                0
% 1.88/0.99  fd_pseudo_cond:                         1
% 1.88/0.99  ac_symbols:                             0
% 1.88/0.99  
% 1.88/0.99  ------ Propositional Solver
% 1.88/0.99  
% 1.88/0.99  prop_solver_calls:                      26
% 1.88/0.99  prop_fast_solver_calls:                 1263
% 1.88/0.99  smt_solver_calls:                       0
% 1.88/0.99  smt_fast_solver_calls:                  0
% 1.88/0.99  prop_num_of_clauses:                    725
% 1.88/0.99  prop_preprocess_simplified:             3488
% 1.88/0.99  prop_fo_subsumed:                       49
% 1.88/0.99  prop_solver_time:                       0.
% 1.88/0.99  smt_solver_time:                        0.
% 1.88/0.99  smt_fast_solver_time:                   0.
% 1.88/0.99  prop_fast_solver_time:                  0.
% 1.88/0.99  prop_unsat_core_time:                   0.
% 1.88/0.99  
% 1.88/0.99  ------ QBF
% 1.88/0.99  
% 1.88/0.99  qbf_q_res:                              0
% 1.88/0.99  qbf_num_tautologies:                    0
% 1.88/0.99  qbf_prep_cycles:                        0
% 1.88/0.99  
% 1.88/0.99  ------ BMC1
% 1.88/0.99  
% 1.88/0.99  bmc1_current_bound:                     -1
% 1.88/0.99  bmc1_last_solved_bound:                 -1
% 1.88/0.99  bmc1_unsat_core_size:                   -1
% 1.88/0.99  bmc1_unsat_core_parents_size:           -1
% 1.88/0.99  bmc1_merge_next_fun:                    0
% 1.88/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.88/0.99  
% 1.88/0.99  ------ Instantiation
% 1.88/0.99  
% 1.88/0.99  inst_num_of_clauses:                    171
% 1.88/0.99  inst_num_in_passive:                    40
% 1.88/0.99  inst_num_in_active:                     104
% 1.88/0.99  inst_num_in_unprocessed:                27
% 1.88/0.99  inst_num_of_loops:                      110
% 1.88/0.99  inst_num_of_learning_restarts:          0
% 1.88/0.99  inst_num_moves_active_passive:          4
% 1.88/0.99  inst_lit_activity:                      0
% 1.88/0.99  inst_lit_activity_moves:                0
% 1.88/0.99  inst_num_tautologies:                   0
% 1.88/0.99  inst_num_prop_implied:                  0
% 1.88/0.99  inst_num_existing_simplified:           0
% 1.88/0.99  inst_num_eq_res_simplified:             0
% 1.88/0.99  inst_num_child_elim:                    0
% 1.88/0.99  inst_num_of_dismatching_blockings:      14
% 1.88/0.99  inst_num_of_non_proper_insts:           156
% 1.88/0.99  inst_num_of_duplicates:                 0
% 1.88/0.99  inst_inst_num_from_inst_to_res:         0
% 1.88/0.99  inst_dismatching_checking_time:         0.
% 1.88/0.99  
% 1.88/0.99  ------ Resolution
% 1.88/0.99  
% 1.88/0.99  res_num_of_clauses:                     0
% 1.88/0.99  res_num_in_passive:                     0
% 1.88/0.99  res_num_in_active:                      0
% 1.88/0.99  res_num_of_loops:                       123
% 1.88/0.99  res_forward_subset_subsumed:            30
% 1.88/0.99  res_backward_subset_subsumed:           0
% 1.88/0.99  res_forward_subsumed:                   0
% 1.88/0.99  res_backward_subsumed:                  0
% 1.88/0.99  res_forward_subsumption_resolution:     2
% 1.88/0.99  res_backward_subsumption_resolution:    1
% 1.88/0.99  res_clause_to_clause_subsumption:       104
% 1.88/0.99  res_orphan_elimination:                 0
% 1.88/0.99  res_tautology_del:                      44
% 1.88/0.99  res_num_eq_res_simplified:              2
% 1.88/0.99  res_num_sel_changes:                    0
% 1.88/0.99  res_moves_from_active_to_pass:          0
% 1.88/0.99  
% 1.88/0.99  ------ Superposition
% 1.88/0.99  
% 1.88/0.99  sup_time_total:                         0.
% 1.88/0.99  sup_time_generating:                    0.
% 1.88/0.99  sup_time_sim_full:                      0.
% 1.88/0.99  sup_time_sim_immed:                     0.
% 1.88/0.99  
% 1.88/0.99  sup_num_of_clauses:                     24
% 1.88/0.99  sup_num_in_active:                      21
% 1.88/0.99  sup_num_in_passive:                     3
% 1.88/0.99  sup_num_of_loops:                       21
% 1.88/0.99  sup_fw_superposition:                   4
% 1.88/0.99  sup_bw_superposition:                   2
% 1.88/0.99  sup_immediate_simplified:               0
% 1.88/0.99  sup_given_eliminated:                   0
% 1.88/0.99  comparisons_done:                       0
% 1.88/0.99  comparisons_avoided:                    0
% 1.88/0.99  
% 1.88/0.99  ------ Simplifications
% 1.88/0.99  
% 1.88/0.99  
% 1.88/0.99  sim_fw_subset_subsumed:                 0
% 1.88/0.99  sim_bw_subset_subsumed:                 1
% 1.88/0.99  sim_fw_subsumed:                        0
% 1.88/0.99  sim_bw_subsumed:                        0
% 1.88/0.99  sim_fw_subsumption_res:                 1
% 1.88/0.99  sim_bw_subsumption_res:                 0
% 1.88/0.99  sim_tautology_del:                      0
% 1.88/0.99  sim_eq_tautology_del:                   1
% 1.88/0.99  sim_eq_res_simp:                        0
% 1.88/0.99  sim_fw_demodulated:                     0
% 1.88/0.99  sim_bw_demodulated:                     0
% 1.88/0.99  sim_light_normalised:                   4
% 1.88/0.99  sim_joinable_taut:                      0
% 1.88/0.99  sim_joinable_simp:                      0
% 1.88/0.99  sim_ac_normalised:                      0
% 1.88/0.99  sim_smt_subsumption:                    0
% 1.88/0.99  
%------------------------------------------------------------------------------
