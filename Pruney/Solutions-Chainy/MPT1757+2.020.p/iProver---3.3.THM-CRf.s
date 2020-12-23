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

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 736 expanded)
%              Number of clauses        :   96 ( 121 expanded)
%              Number of leaves         :   20 ( 289 expanded)
%              Depth                    :   27
%              Number of atoms          : 1384 (11696 expanded)
%              Number of equality atoms :  119 ( 847 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f49,f55,f54,f53,f52,f51,f50])).

fof(f90,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f47,plain,(
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

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f102,plain,(
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
    inference(equality_resolution,[],[f78])).

fof(f86,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f56])).

fof(f85,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f83,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f84,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f80,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f79,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f81,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK0(X0,X1,X2))
        & r1_tarski(sK0(X0,X1,X2),X2)
        & v3_pre_topc(sK0(X0,X1,X2),X0)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK0(X0,X1,X2))
                    & r1_tarski(sK0(X0,X1,X2),X2)
                    & v3_pre_topc(sK0(X0,X1,X2),X0)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f63,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f95,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | ~ r1_tmap_1(sK2,sK1,sK3,sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f93,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f56])).

fof(f92,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f56])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f103,plain,(
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
    inference(equality_resolution,[],[f77])).

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

fof(f76,plain,(
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
    inference(equality_resolution,[],[f76])).

fof(f94,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | r1_tmap_1(sK2,sK1,sK3,sK5) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f89,plain,(
    v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f90])).

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
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_858,plain,
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
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_859,plain,
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
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_858])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_863,plain,
    ( ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_connsp_2(X4,X2,X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_859,c_32])).

cnf(c_864,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_863])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_905,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_864,c_8])).

cnf(c_1015,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_905])).

cnf(c_1016,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_connsp_2(X2,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1015])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1020,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_connsp_2(X2,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1016,c_35,c_34,c_33,c_29])).

cnf(c_1021,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_connsp_2(X2,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1020])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1449,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_connsp_2(X2,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1021,c_37])).

cnf(c_1450,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_connsp_2(X1,sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1449])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1454,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_connsp_2(X1,sK2,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1450,c_38,c_36,c_30])).

cnf(c_1455,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_connsp_2(X1,sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1454])).

cnf(c_3388,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_connsp_2(X1,sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,u1_struct_0(sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1455])).

cnf(c_6043,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | ~ m1_connsp_2(X0,sK2,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3388])).

cnf(c_6956,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | ~ m1_connsp_2(u1_struct_0(sK4),sK2,sK6)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6043])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_6622,plain,
    ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1566,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_34])).

cnf(c_1567,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X2,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1566])).

cnf(c_1571,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X2,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1567,c_35,c_33])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1591,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X2,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1571,c_4])).

cnf(c_6048,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(u1_struct_0(sK4),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_1591])).

cnf(c_6451,plain,
    ( m1_connsp_2(X0,sK2,sK6)
    | ~ v3_pre_topc(u1_struct_0(sK4),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK6,u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_6048])).

cnf(c_6621,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK2,sK6)
    | ~ v3_pre_topc(u1_struct_0(sK4),sK2)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK6,u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6451])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_5,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_513,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_5,c_7])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1004,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_27])).

cnf(c_1005,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1004])).

cnf(c_1007,plain,
    ( l1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1005,c_33])).

cnf(c_1866,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_513,c_1007])).

cnf(c_1867,plain,
    ( v2_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_1866])).

cnf(c_1869,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1867,c_29])).

cnf(c_1907,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | u1_struct_0(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_1869])).

cnf(c_1908,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_1907])).

cnf(c_6065,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | r2_hidden(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1908])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_5739,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK5) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_24,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_5791,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5739,c_24])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_52,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

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
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f101])).

cnf(c_206,plain,
    ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
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
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_19])).

cnf(c_207,plain,
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
    inference(renaming,[status(thm)],[c_206])).

cnf(c_801,plain,
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
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_207,c_31])).

cnf(c_802,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_801])).

cnf(c_806,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_802,c_32])).

cnf(c_807,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_806])).

cnf(c_842,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_807,c_8])).

cnf(c_1063,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_842])).

cnf(c_1064,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1063])).

cnf(c_1068,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1064,c_35,c_34,c_33,c_29])).

cnf(c_1069,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1068])).

cnf(c_1425,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1069,c_37])).

cnf(c_1426,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1425])).

cnf(c_1430,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1426,c_38,c_36,c_30])).

cnf(c_1431,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1430])).

cnf(c_3392,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1431])).

cnf(c_6040,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3392])).

cnf(c_6041,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6040])).

cnf(c_6054,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5791,c_52,c_6041])).

cnf(c_6056,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6054])).

cnf(c_23,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,sK3,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_5738,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK5) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5780,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5738,c_24])).

cnf(c_5940,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5780])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_975,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_976,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_975])).

cnf(c_17,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_214,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_18])).

cnf(c_215,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_214])).

cnf(c_28,negated_conjecture,
    ( v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_554,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_215,c_28])).

cnf(c_555,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6956,c_6622,c_6621,c_6065,c_6056,c_5940,c_976,c_555,c_25,c_27,c_33,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.33/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.01  
% 2.33/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.33/1.01  
% 2.33/1.01  ------  iProver source info
% 2.33/1.01  
% 2.33/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.33/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.33/1.01  git: non_committed_changes: false
% 2.33/1.01  git: last_make_outside_of_git: false
% 2.33/1.01  
% 2.33/1.01  ------ 
% 2.33/1.01  
% 2.33/1.01  ------ Input Options
% 2.33/1.01  
% 2.33/1.01  --out_options                           all
% 2.33/1.01  --tptp_safe_out                         true
% 2.33/1.01  --problem_path                          ""
% 2.33/1.01  --include_path                          ""
% 2.33/1.01  --clausifier                            res/vclausify_rel
% 2.33/1.01  --clausifier_options                    --mode clausify
% 2.33/1.01  --stdin                                 false
% 2.33/1.01  --stats_out                             all
% 2.33/1.01  
% 2.33/1.01  ------ General Options
% 2.33/1.01  
% 2.33/1.01  --fof                                   false
% 2.33/1.01  --time_out_real                         305.
% 2.33/1.01  --time_out_virtual                      -1.
% 2.33/1.01  --symbol_type_check                     false
% 2.33/1.01  --clausify_out                          false
% 2.33/1.01  --sig_cnt_out                           false
% 2.33/1.01  --trig_cnt_out                          false
% 2.33/1.01  --trig_cnt_out_tolerance                1.
% 2.33/1.01  --trig_cnt_out_sk_spl                   false
% 2.33/1.01  --abstr_cl_out                          false
% 2.33/1.01  
% 2.33/1.01  ------ Global Options
% 2.33/1.01  
% 2.33/1.01  --schedule                              default
% 2.33/1.01  --add_important_lit                     false
% 2.33/1.01  --prop_solver_per_cl                    1000
% 2.33/1.01  --min_unsat_core                        false
% 2.33/1.01  --soft_assumptions                      false
% 2.33/1.01  --soft_lemma_size                       3
% 2.33/1.01  --prop_impl_unit_size                   0
% 2.33/1.01  --prop_impl_unit                        []
% 2.33/1.01  --share_sel_clauses                     true
% 2.33/1.01  --reset_solvers                         false
% 2.33/1.01  --bc_imp_inh                            [conj_cone]
% 2.33/1.01  --conj_cone_tolerance                   3.
% 2.33/1.01  --extra_neg_conj                        none
% 2.33/1.01  --large_theory_mode                     true
% 2.33/1.01  --prolific_symb_bound                   200
% 2.33/1.01  --lt_threshold                          2000
% 2.33/1.01  --clause_weak_htbl                      true
% 2.33/1.01  --gc_record_bc_elim                     false
% 2.33/1.01  
% 2.33/1.01  ------ Preprocessing Options
% 2.33/1.01  
% 2.33/1.01  --preprocessing_flag                    true
% 2.33/1.01  --time_out_prep_mult                    0.1
% 2.33/1.01  --splitting_mode                        input
% 2.33/1.01  --splitting_grd                         true
% 2.33/1.01  --splitting_cvd                         false
% 2.33/1.01  --splitting_cvd_svl                     false
% 2.33/1.01  --splitting_nvd                         32
% 2.33/1.01  --sub_typing                            true
% 2.33/1.01  --prep_gs_sim                           true
% 2.33/1.01  --prep_unflatten                        true
% 2.33/1.01  --prep_res_sim                          true
% 2.33/1.01  --prep_upred                            true
% 2.33/1.01  --prep_sem_filter                       exhaustive
% 2.33/1.01  --prep_sem_filter_out                   false
% 2.33/1.01  --pred_elim                             true
% 2.33/1.01  --res_sim_input                         true
% 2.33/1.01  --eq_ax_congr_red                       true
% 2.33/1.01  --pure_diseq_elim                       true
% 2.33/1.01  --brand_transform                       false
% 2.33/1.01  --non_eq_to_eq                          false
% 2.33/1.01  --prep_def_merge                        true
% 2.33/1.01  --prep_def_merge_prop_impl              false
% 2.33/1.01  --prep_def_merge_mbd                    true
% 2.33/1.01  --prep_def_merge_tr_red                 false
% 2.33/1.01  --prep_def_merge_tr_cl                  false
% 2.33/1.01  --smt_preprocessing                     true
% 2.33/1.01  --smt_ac_axioms                         fast
% 2.33/1.01  --preprocessed_out                      false
% 2.33/1.01  --preprocessed_stats                    false
% 2.33/1.01  
% 2.33/1.01  ------ Abstraction refinement Options
% 2.33/1.01  
% 2.33/1.01  --abstr_ref                             []
% 2.33/1.01  --abstr_ref_prep                        false
% 2.33/1.01  --abstr_ref_until_sat                   false
% 2.33/1.01  --abstr_ref_sig_restrict                funpre
% 2.33/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/1.01  --abstr_ref_under                       []
% 2.33/1.01  
% 2.33/1.01  ------ SAT Options
% 2.33/1.01  
% 2.33/1.01  --sat_mode                              false
% 2.33/1.01  --sat_fm_restart_options                ""
% 2.33/1.01  --sat_gr_def                            false
% 2.33/1.01  --sat_epr_types                         true
% 2.33/1.01  --sat_non_cyclic_types                  false
% 2.33/1.01  --sat_finite_models                     false
% 2.33/1.01  --sat_fm_lemmas                         false
% 2.33/1.01  --sat_fm_prep                           false
% 2.33/1.01  --sat_fm_uc_incr                        true
% 2.33/1.01  --sat_out_model                         small
% 2.33/1.01  --sat_out_clauses                       false
% 2.33/1.01  
% 2.33/1.01  ------ QBF Options
% 2.33/1.01  
% 2.33/1.01  --qbf_mode                              false
% 2.33/1.01  --qbf_elim_univ                         false
% 2.33/1.01  --qbf_dom_inst                          none
% 2.33/1.01  --qbf_dom_pre_inst                      false
% 2.33/1.01  --qbf_sk_in                             false
% 2.33/1.01  --qbf_pred_elim                         true
% 2.33/1.01  --qbf_split                             512
% 2.33/1.01  
% 2.33/1.01  ------ BMC1 Options
% 2.33/1.01  
% 2.33/1.01  --bmc1_incremental                      false
% 2.33/1.01  --bmc1_axioms                           reachable_all
% 2.33/1.01  --bmc1_min_bound                        0
% 2.33/1.01  --bmc1_max_bound                        -1
% 2.33/1.01  --bmc1_max_bound_default                -1
% 2.33/1.01  --bmc1_symbol_reachability              true
% 2.33/1.01  --bmc1_property_lemmas                  false
% 2.33/1.01  --bmc1_k_induction                      false
% 2.33/1.01  --bmc1_non_equiv_states                 false
% 2.33/1.01  --bmc1_deadlock                         false
% 2.33/1.01  --bmc1_ucm                              false
% 2.33/1.01  --bmc1_add_unsat_core                   none
% 2.33/1.01  --bmc1_unsat_core_children              false
% 2.33/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/1.01  --bmc1_out_stat                         full
% 2.33/1.01  --bmc1_ground_init                      false
% 2.33/1.01  --bmc1_pre_inst_next_state              false
% 2.33/1.01  --bmc1_pre_inst_state                   false
% 2.33/1.01  --bmc1_pre_inst_reach_state             false
% 2.33/1.01  --bmc1_out_unsat_core                   false
% 2.33/1.01  --bmc1_aig_witness_out                  false
% 2.33/1.01  --bmc1_verbose                          false
% 2.33/1.01  --bmc1_dump_clauses_tptp                false
% 2.33/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.33/1.01  --bmc1_dump_file                        -
% 2.33/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.33/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.33/1.01  --bmc1_ucm_extend_mode                  1
% 2.33/1.01  --bmc1_ucm_init_mode                    2
% 2.33/1.01  --bmc1_ucm_cone_mode                    none
% 2.33/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.33/1.01  --bmc1_ucm_relax_model                  4
% 2.33/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.33/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/1.01  --bmc1_ucm_layered_model                none
% 2.33/1.01  --bmc1_ucm_max_lemma_size               10
% 2.33/1.01  
% 2.33/1.01  ------ AIG Options
% 2.33/1.01  
% 2.33/1.01  --aig_mode                              false
% 2.33/1.01  
% 2.33/1.01  ------ Instantiation Options
% 2.33/1.01  
% 2.33/1.01  --instantiation_flag                    true
% 2.33/1.01  --inst_sos_flag                         false
% 2.33/1.01  --inst_sos_phase                        true
% 2.33/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/1.01  --inst_lit_sel_side                     num_symb
% 2.33/1.01  --inst_solver_per_active                1400
% 2.33/1.01  --inst_solver_calls_frac                1.
% 2.33/1.01  --inst_passive_queue_type               priority_queues
% 2.33/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/1.01  --inst_passive_queues_freq              [25;2]
% 2.33/1.01  --inst_dismatching                      true
% 2.33/1.01  --inst_eager_unprocessed_to_passive     true
% 2.33/1.01  --inst_prop_sim_given                   true
% 2.33/1.01  --inst_prop_sim_new                     false
% 2.33/1.01  --inst_subs_new                         false
% 2.33/1.01  --inst_eq_res_simp                      false
% 2.33/1.01  --inst_subs_given                       false
% 2.33/1.01  --inst_orphan_elimination               true
% 2.33/1.01  --inst_learning_loop_flag               true
% 2.33/1.01  --inst_learning_start                   3000
% 2.33/1.01  --inst_learning_factor                  2
% 2.33/1.01  --inst_start_prop_sim_after_learn       3
% 2.33/1.01  --inst_sel_renew                        solver
% 2.33/1.01  --inst_lit_activity_flag                true
% 2.33/1.01  --inst_restr_to_given                   false
% 2.33/1.01  --inst_activity_threshold               500
% 2.33/1.01  --inst_out_proof                        true
% 2.33/1.01  
% 2.33/1.01  ------ Resolution Options
% 2.33/1.01  
% 2.33/1.01  --resolution_flag                       true
% 2.33/1.01  --res_lit_sel                           adaptive
% 2.33/1.01  --res_lit_sel_side                      none
% 2.33/1.01  --res_ordering                          kbo
% 2.33/1.01  --res_to_prop_solver                    active
% 2.33/1.01  --res_prop_simpl_new                    false
% 2.33/1.01  --res_prop_simpl_given                  true
% 2.33/1.01  --res_passive_queue_type                priority_queues
% 2.33/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/1.01  --res_passive_queues_freq               [15;5]
% 2.33/1.01  --res_forward_subs                      full
% 2.33/1.01  --res_backward_subs                     full
% 2.33/1.01  --res_forward_subs_resolution           true
% 2.33/1.01  --res_backward_subs_resolution          true
% 2.33/1.01  --res_orphan_elimination                true
% 2.33/1.01  --res_time_limit                        2.
% 2.33/1.01  --res_out_proof                         true
% 2.33/1.01  
% 2.33/1.01  ------ Superposition Options
% 2.33/1.01  
% 2.33/1.01  --superposition_flag                    true
% 2.33/1.01  --sup_passive_queue_type                priority_queues
% 2.33/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.33/1.01  --demod_completeness_check              fast
% 2.33/1.01  --demod_use_ground                      true
% 2.33/1.01  --sup_to_prop_solver                    passive
% 2.33/1.01  --sup_prop_simpl_new                    true
% 2.33/1.01  --sup_prop_simpl_given                  true
% 2.33/1.01  --sup_fun_splitting                     false
% 2.33/1.01  --sup_smt_interval                      50000
% 2.33/1.01  
% 2.33/1.01  ------ Superposition Simplification Setup
% 2.33/1.01  
% 2.33/1.01  --sup_indices_passive                   []
% 2.33/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.01  --sup_full_bw                           [BwDemod]
% 2.33/1.01  --sup_immed_triv                        [TrivRules]
% 2.33/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.01  --sup_immed_bw_main                     []
% 2.33/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.01  
% 2.33/1.01  ------ Combination Options
% 2.33/1.01  
% 2.33/1.01  --comb_res_mult                         3
% 2.33/1.01  --comb_sup_mult                         2
% 2.33/1.01  --comb_inst_mult                        10
% 2.33/1.01  
% 2.33/1.01  ------ Debug Options
% 2.33/1.01  
% 2.33/1.01  --dbg_backtrace                         false
% 2.33/1.01  --dbg_dump_prop_clauses                 false
% 2.33/1.01  --dbg_dump_prop_clauses_file            -
% 2.33/1.01  --dbg_out_stat                          false
% 2.33/1.01  ------ Parsing...
% 2.33/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.33/1.01  
% 2.33/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.33/1.01  
% 2.33/1.01  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/1.01  
% 2.33/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/1.01  ------ Proving...
% 2.33/1.01  ------ Problem Properties 
% 2.33/1.01  
% 2.33/1.01  
% 2.33/1.01  clauses                                 33
% 2.33/1.01  conjectures                             6
% 2.33/1.01  EPR                                     3
% 2.33/1.01  Horn                                    32
% 2.33/1.01  unary                                   7
% 2.33/1.01  binary                                  6
% 2.33/1.01  lits                                    93
% 2.33/1.01  lits eq                                 4
% 2.33/1.01  fd_pure                                 0
% 2.33/1.01  fd_pseudo                               0
% 2.33/1.01  fd_cond                                 0
% 2.33/1.01  fd_pseudo_cond                          1
% 2.33/1.01  AC symbols                              0
% 2.33/1.01  
% 2.33/1.01  ------ Schedule dynamic 5 is on 
% 2.33/1.01  
% 2.33/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.33/1.01  
% 2.33/1.01  
% 2.33/1.01  ------ 
% 2.33/1.01  Current options:
% 2.33/1.01  ------ 
% 2.33/1.01  
% 2.33/1.01  ------ Input Options
% 2.33/1.01  
% 2.33/1.01  --out_options                           all
% 2.33/1.01  --tptp_safe_out                         true
% 2.33/1.01  --problem_path                          ""
% 2.33/1.01  --include_path                          ""
% 2.33/1.01  --clausifier                            res/vclausify_rel
% 2.33/1.01  --clausifier_options                    --mode clausify
% 2.33/1.01  --stdin                                 false
% 2.33/1.01  --stats_out                             all
% 2.33/1.01  
% 2.33/1.01  ------ General Options
% 2.33/1.01  
% 2.33/1.01  --fof                                   false
% 2.33/1.01  --time_out_real                         305.
% 2.33/1.01  --time_out_virtual                      -1.
% 2.33/1.01  --symbol_type_check                     false
% 2.33/1.01  --clausify_out                          false
% 2.33/1.01  --sig_cnt_out                           false
% 2.33/1.01  --trig_cnt_out                          false
% 2.33/1.01  --trig_cnt_out_tolerance                1.
% 2.33/1.01  --trig_cnt_out_sk_spl                   false
% 2.33/1.01  --abstr_cl_out                          false
% 2.33/1.01  
% 2.33/1.01  ------ Global Options
% 2.33/1.01  
% 2.33/1.01  --schedule                              default
% 2.33/1.01  --add_important_lit                     false
% 2.33/1.01  --prop_solver_per_cl                    1000
% 2.33/1.01  --min_unsat_core                        false
% 2.33/1.01  --soft_assumptions                      false
% 2.33/1.01  --soft_lemma_size                       3
% 2.33/1.01  --prop_impl_unit_size                   0
% 2.33/1.01  --prop_impl_unit                        []
% 2.33/1.01  --share_sel_clauses                     true
% 2.33/1.01  --reset_solvers                         false
% 2.33/1.01  --bc_imp_inh                            [conj_cone]
% 2.33/1.01  --conj_cone_tolerance                   3.
% 2.33/1.01  --extra_neg_conj                        none
% 2.33/1.01  --large_theory_mode                     true
% 2.33/1.01  --prolific_symb_bound                   200
% 2.33/1.01  --lt_threshold                          2000
% 2.33/1.01  --clause_weak_htbl                      true
% 2.33/1.01  --gc_record_bc_elim                     false
% 2.33/1.01  
% 2.33/1.01  ------ Preprocessing Options
% 2.33/1.01  
% 2.33/1.01  --preprocessing_flag                    true
% 2.33/1.01  --time_out_prep_mult                    0.1
% 2.33/1.01  --splitting_mode                        input
% 2.33/1.01  --splitting_grd                         true
% 2.33/1.01  --splitting_cvd                         false
% 2.33/1.01  --splitting_cvd_svl                     false
% 2.33/1.01  --splitting_nvd                         32
% 2.33/1.01  --sub_typing                            true
% 2.33/1.01  --prep_gs_sim                           true
% 2.33/1.01  --prep_unflatten                        true
% 2.33/1.01  --prep_res_sim                          true
% 2.33/1.01  --prep_upred                            true
% 2.33/1.01  --prep_sem_filter                       exhaustive
% 2.33/1.01  --prep_sem_filter_out                   false
% 2.33/1.01  --pred_elim                             true
% 2.33/1.01  --res_sim_input                         true
% 2.33/1.01  --eq_ax_congr_red                       true
% 2.33/1.01  --pure_diseq_elim                       true
% 2.33/1.01  --brand_transform                       false
% 2.33/1.01  --non_eq_to_eq                          false
% 2.33/1.01  --prep_def_merge                        true
% 2.33/1.01  --prep_def_merge_prop_impl              false
% 2.33/1.01  --prep_def_merge_mbd                    true
% 2.33/1.01  --prep_def_merge_tr_red                 false
% 2.33/1.01  --prep_def_merge_tr_cl                  false
% 2.33/1.01  --smt_preprocessing                     true
% 2.33/1.01  --smt_ac_axioms                         fast
% 2.33/1.01  --preprocessed_out                      false
% 2.33/1.01  --preprocessed_stats                    false
% 2.33/1.01  
% 2.33/1.01  ------ Abstraction refinement Options
% 2.33/1.01  
% 2.33/1.01  --abstr_ref                             []
% 2.33/1.01  --abstr_ref_prep                        false
% 2.33/1.01  --abstr_ref_until_sat                   false
% 2.33/1.01  --abstr_ref_sig_restrict                funpre
% 2.33/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/1.01  --abstr_ref_under                       []
% 2.33/1.01  
% 2.33/1.01  ------ SAT Options
% 2.33/1.01  
% 2.33/1.01  --sat_mode                              false
% 2.33/1.01  --sat_fm_restart_options                ""
% 2.33/1.01  --sat_gr_def                            false
% 2.33/1.01  --sat_epr_types                         true
% 2.33/1.01  --sat_non_cyclic_types                  false
% 2.33/1.01  --sat_finite_models                     false
% 2.33/1.01  --sat_fm_lemmas                         false
% 2.33/1.01  --sat_fm_prep                           false
% 2.33/1.01  --sat_fm_uc_incr                        true
% 2.33/1.01  --sat_out_model                         small
% 2.33/1.01  --sat_out_clauses                       false
% 2.33/1.01  
% 2.33/1.01  ------ QBF Options
% 2.33/1.01  
% 2.33/1.01  --qbf_mode                              false
% 2.33/1.01  --qbf_elim_univ                         false
% 2.33/1.01  --qbf_dom_inst                          none
% 2.33/1.01  --qbf_dom_pre_inst                      false
% 2.33/1.01  --qbf_sk_in                             false
% 2.33/1.01  --qbf_pred_elim                         true
% 2.33/1.01  --qbf_split                             512
% 2.33/1.01  
% 2.33/1.01  ------ BMC1 Options
% 2.33/1.01  
% 2.33/1.01  --bmc1_incremental                      false
% 2.33/1.01  --bmc1_axioms                           reachable_all
% 2.33/1.01  --bmc1_min_bound                        0
% 2.33/1.01  --bmc1_max_bound                        -1
% 2.33/1.01  --bmc1_max_bound_default                -1
% 2.33/1.01  --bmc1_symbol_reachability              true
% 2.33/1.01  --bmc1_property_lemmas                  false
% 2.33/1.01  --bmc1_k_induction                      false
% 2.33/1.01  --bmc1_non_equiv_states                 false
% 2.33/1.01  --bmc1_deadlock                         false
% 2.33/1.01  --bmc1_ucm                              false
% 2.33/1.01  --bmc1_add_unsat_core                   none
% 2.33/1.01  --bmc1_unsat_core_children              false
% 2.33/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/1.01  --bmc1_out_stat                         full
% 2.33/1.01  --bmc1_ground_init                      false
% 2.33/1.01  --bmc1_pre_inst_next_state              false
% 2.33/1.01  --bmc1_pre_inst_state                   false
% 2.33/1.01  --bmc1_pre_inst_reach_state             false
% 2.33/1.01  --bmc1_out_unsat_core                   false
% 2.33/1.01  --bmc1_aig_witness_out                  false
% 2.33/1.01  --bmc1_verbose                          false
% 2.33/1.01  --bmc1_dump_clauses_tptp                false
% 2.33/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.33/1.01  --bmc1_dump_file                        -
% 2.33/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.33/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.33/1.01  --bmc1_ucm_extend_mode                  1
% 2.33/1.01  --bmc1_ucm_init_mode                    2
% 2.33/1.01  --bmc1_ucm_cone_mode                    none
% 2.33/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.33/1.01  --bmc1_ucm_relax_model                  4
% 2.33/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.33/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/1.01  --bmc1_ucm_layered_model                none
% 2.33/1.01  --bmc1_ucm_max_lemma_size               10
% 2.33/1.01  
% 2.33/1.01  ------ AIG Options
% 2.33/1.01  
% 2.33/1.01  --aig_mode                              false
% 2.33/1.01  
% 2.33/1.01  ------ Instantiation Options
% 2.33/1.01  
% 2.33/1.01  --instantiation_flag                    true
% 2.33/1.01  --inst_sos_flag                         false
% 2.33/1.01  --inst_sos_phase                        true
% 2.33/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/1.01  --inst_lit_sel_side                     none
% 2.33/1.01  --inst_solver_per_active                1400
% 2.33/1.01  --inst_solver_calls_frac                1.
% 2.33/1.01  --inst_passive_queue_type               priority_queues
% 2.33/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/1.01  --inst_passive_queues_freq              [25;2]
% 2.33/1.01  --inst_dismatching                      true
% 2.33/1.01  --inst_eager_unprocessed_to_passive     true
% 2.33/1.01  --inst_prop_sim_given                   true
% 2.33/1.01  --inst_prop_sim_new                     false
% 2.33/1.01  --inst_subs_new                         false
% 2.33/1.01  --inst_eq_res_simp                      false
% 2.33/1.01  --inst_subs_given                       false
% 2.33/1.01  --inst_orphan_elimination               true
% 2.33/1.01  --inst_learning_loop_flag               true
% 2.33/1.01  --inst_learning_start                   3000
% 2.33/1.01  --inst_learning_factor                  2
% 2.33/1.01  --inst_start_prop_sim_after_learn       3
% 2.33/1.01  --inst_sel_renew                        solver
% 2.33/1.01  --inst_lit_activity_flag                true
% 2.33/1.01  --inst_restr_to_given                   false
% 2.33/1.01  --inst_activity_threshold               500
% 2.33/1.01  --inst_out_proof                        true
% 2.33/1.01  
% 2.33/1.01  ------ Resolution Options
% 2.33/1.01  
% 2.33/1.01  --resolution_flag                       false
% 2.33/1.01  --res_lit_sel                           adaptive
% 2.33/1.01  --res_lit_sel_side                      none
% 2.33/1.01  --res_ordering                          kbo
% 2.33/1.01  --res_to_prop_solver                    active
% 2.33/1.01  --res_prop_simpl_new                    false
% 2.33/1.01  --res_prop_simpl_given                  true
% 2.33/1.01  --res_passive_queue_type                priority_queues
% 2.33/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/1.01  --res_passive_queues_freq               [15;5]
% 2.33/1.01  --res_forward_subs                      full
% 2.33/1.01  --res_backward_subs                     full
% 2.33/1.01  --res_forward_subs_resolution           true
% 2.33/1.01  --res_backward_subs_resolution          true
% 2.33/1.01  --res_orphan_elimination                true
% 2.33/1.01  --res_time_limit                        2.
% 2.33/1.01  --res_out_proof                         true
% 2.33/1.01  
% 2.33/1.01  ------ Superposition Options
% 2.33/1.01  
% 2.33/1.01  --superposition_flag                    true
% 2.33/1.01  --sup_passive_queue_type                priority_queues
% 2.33/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.33/1.01  --demod_completeness_check              fast
% 2.33/1.01  --demod_use_ground                      true
% 2.33/1.01  --sup_to_prop_solver                    passive
% 2.33/1.01  --sup_prop_simpl_new                    true
% 2.33/1.01  --sup_prop_simpl_given                  true
% 2.33/1.01  --sup_fun_splitting                     false
% 2.33/1.01  --sup_smt_interval                      50000
% 2.33/1.01  
% 2.33/1.01  ------ Superposition Simplification Setup
% 2.33/1.01  
% 2.33/1.01  --sup_indices_passive                   []
% 2.33/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.01  --sup_full_bw                           [BwDemod]
% 2.33/1.01  --sup_immed_triv                        [TrivRules]
% 2.33/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.01  --sup_immed_bw_main                     []
% 2.33/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.01  
% 2.33/1.01  ------ Combination Options
% 2.33/1.01  
% 2.33/1.01  --comb_res_mult                         3
% 2.33/1.01  --comb_sup_mult                         2
% 2.33/1.01  --comb_inst_mult                        10
% 2.33/1.01  
% 2.33/1.01  ------ Debug Options
% 2.33/1.01  
% 2.33/1.01  --dbg_backtrace                         false
% 2.33/1.01  --dbg_dump_prop_clauses                 false
% 2.33/1.01  --dbg_dump_prop_clauses_file            -
% 2.33/1.01  --dbg_out_stat                          false
% 2.33/1.01  
% 2.33/1.01  
% 2.33/1.01  
% 2.33/1.01  
% 2.33/1.01  ------ Proving...
% 2.33/1.01  
% 2.33/1.01  
% 2.33/1.01  % SZS status Theorem for theBenchmark.p
% 2.33/1.01  
% 2.33/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.33/1.01  
% 2.33/1.01  fof(f14,conjecture,(
% 2.33/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.33/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.01  
% 2.33/1.01  fof(f15,negated_conjecture,(
% 2.33/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.33/1.01    inference(negated_conjecture,[],[f14])).
% 2.33/1.01  
% 2.33/1.01  fof(f37,plain,(
% 2.33/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.33/1.01    inference(ennf_transformation,[],[f15])).
% 2.33/1.01  
% 2.33/1.01  fof(f38,plain,(
% 2.33/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.33/1.01    inference(flattening,[],[f37])).
% 2.33/1.01  
% 2.33/1.01  fof(f48,plain,(
% 2.33/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.33/1.01    inference(nnf_transformation,[],[f38])).
% 2.33/1.01  
% 2.33/1.01  fof(f49,plain,(
% 2.33/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.33/1.01    inference(flattening,[],[f48])).
% 2.33/1.01  
% 2.33/1.01  fof(f55,plain,(
% 2.33/1.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6) | r1_tmap_1(X1,X0,X2,X4)) & sK6 = X4 & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.33/1.01    introduced(choice_axiom,[])).
% 2.33/1.01  
% 2.33/1.01  fof(f54,plain,(
% 2.33/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK5)) & sK5 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK5,u1_struct_0(X1)))) )),
% 2.33/1.01    introduced(choice_axiom,[])).
% 2.33/1.01  
% 2.33/1.01  fof(f53,plain,(
% 2.33/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK4,X1) & v1_tsep_1(sK4,X1) & ~v2_struct_0(sK4))) )),
% 2.33/1.01    introduced(choice_axiom,[])).
% 2.33/1.01  
% 2.33/1.01  fof(f52,plain,(
% 2.33/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X5) | ~r1_tmap_1(X1,X0,sK3,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X5) | r1_tmap_1(X1,X0,sK3,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 2.33/1.01    introduced(choice_axiom,[])).
% 2.33/1.01  
% 2.33/1.01  fof(f51,plain,(
% 2.33/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X5) | ~r1_tmap_1(sK2,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X5) | r1_tmap_1(sK2,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK2))) & m1_pre_topc(X3,sK2) & v1_tsep_1(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.33/1.01    introduced(choice_axiom,[])).
% 2.33/1.01  
% 2.33/1.01  fof(f50,plain,(
% 2.33/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X5) | ~r1_tmap_1(X1,sK1,X2,X4)) & (r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X5) | r1_tmap_1(X1,sK1,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.33/1.01    introduced(choice_axiom,[])).
% 2.33/1.01  
% 2.33/1.01  fof(f56,plain,(
% 2.33/1.01    ((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | ~r1_tmap_1(sK2,sK1,sK3,sK5)) & (r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | r1_tmap_1(sK2,sK1,sK3,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK2))) & m1_pre_topc(sK4,sK2) & v1_tsep_1(sK4,sK2) & ~v2_struct_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.33/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f49,f55,f54,f53,f52,f51,f50])).
% 2.33/1.01  
% 2.33/1.01  fof(f90,plain,(
% 2.33/1.01    m1_pre_topc(sK4,sK2)),
% 2.33/1.01    inference(cnf_transformation,[],[f56])).
% 2.33/1.01  
% 2.33/1.01  fof(f13,axiom,(
% 2.33/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.33/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.01  
% 2.33/1.01  fof(f35,plain,(
% 2.33/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/1.01    inference(ennf_transformation,[],[f13])).
% 2.33/1.01  
% 2.33/1.01  fof(f36,plain,(
% 2.33/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.01    inference(flattening,[],[f35])).
% 2.33/1.01  
% 2.33/1.01  fof(f47,plain,(
% 2.33/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.01    inference(nnf_transformation,[],[f36])).
% 2.33/1.01  
% 2.33/1.01  fof(f78,plain,(
% 2.33/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.01    inference(cnf_transformation,[],[f47])).
% 2.33/1.01  
% 2.33/1.01  fof(f102,plain,(
% 2.33/1.01    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.01    inference(equality_resolution,[],[f78])).
% 2.33/1.01  
% 2.33/1.01  fof(f86,plain,(
% 2.33/1.01    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.33/1.01    inference(cnf_transformation,[],[f56])).
% 2.33/1.01  
% 2.33/1.01  fof(f85,plain,(
% 2.33/1.01    v1_funct_1(sK3)),
% 2.33/1.01    inference(cnf_transformation,[],[f56])).
% 2.33/1.01  
% 2.33/1.01  fof(f7,axiom,(
% 2.33/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.33/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.01  
% 2.33/1.01  fof(f24,plain,(
% 2.33/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/1.01    inference(ennf_transformation,[],[f7])).
% 2.33/1.01  
% 2.33/1.01  fof(f25,plain,(
% 2.33/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.01    inference(flattening,[],[f24])).
% 2.33/1.01  
% 2.33/1.01  fof(f65,plain,(
% 2.33/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.01    inference(cnf_transformation,[],[f25])).
% 2.33/1.01  
% 2.33/1.01  fof(f82,plain,(
% 2.33/1.01    ~v2_struct_0(sK2)),
% 2.33/1.01    inference(cnf_transformation,[],[f56])).
% 2.33/1.01  
% 2.33/1.01  fof(f83,plain,(
% 2.33/1.01    v2_pre_topc(sK2)),
% 2.33/1.01    inference(cnf_transformation,[],[f56])).
% 2.33/1.01  
% 2.33/1.01  fof(f84,plain,(
% 2.33/1.01    l1_pre_topc(sK2)),
% 2.33/1.01    inference(cnf_transformation,[],[f56])).
% 2.33/1.01  
% 2.33/1.01  fof(f88,plain,(
% 2.33/1.01    ~v2_struct_0(sK4)),
% 2.33/1.01    inference(cnf_transformation,[],[f56])).
% 2.33/1.01  
% 2.33/1.01  fof(f80,plain,(
% 2.33/1.01    v2_pre_topc(sK1)),
% 2.33/1.01    inference(cnf_transformation,[],[f56])).
% 2.33/1.01  
% 2.33/1.01  fof(f79,plain,(
% 2.33/1.01    ~v2_struct_0(sK1)),
% 2.33/1.01    inference(cnf_transformation,[],[f56])).
% 2.33/1.01  
% 2.33/1.01  fof(f81,plain,(
% 2.33/1.01    l1_pre_topc(sK1)),
% 2.33/1.01    inference(cnf_transformation,[],[f56])).
% 2.33/1.01  
% 2.33/1.01  fof(f87,plain,(
% 2.33/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.33/1.01    inference(cnf_transformation,[],[f56])).
% 2.33/1.01  
% 2.33/1.01  fof(f1,axiom,(
% 2.33/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.33/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.01  
% 2.33/1.01  fof(f39,plain,(
% 2.33/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.33/1.01    inference(nnf_transformation,[],[f1])).
% 2.33/1.01  
% 2.33/1.01  fof(f40,plain,(
% 2.33/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.33/1.01    inference(flattening,[],[f39])).
% 2.33/1.01  
% 2.33/1.01  fof(f58,plain,(
% 2.33/1.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.33/1.01    inference(cnf_transformation,[],[f40])).
% 2.33/1.01  
% 2.33/1.01  fof(f96,plain,(
% 2.33/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.33/1.01    inference(equality_resolution,[],[f58])).
% 2.33/1.01  
% 2.33/1.01  fof(f9,axiom,(
% 2.33/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 2.33/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.01  
% 2.33/1.01  fof(f28,plain,(
% 2.33/1.01    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/1.01    inference(ennf_transformation,[],[f9])).
% 2.33/1.01  
% 2.33/1.01  fof(f29,plain,(
% 2.33/1.01    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.01    inference(flattening,[],[f28])).
% 2.33/1.01  
% 2.33/1.01  fof(f41,plain,(
% 2.33/1.01    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.01    inference(nnf_transformation,[],[f29])).
% 2.33/1.01  
% 2.33/1.01  fof(f42,plain,(
% 2.33/1.01    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.01    inference(rectify,[],[f41])).
% 2.33/1.01  
% 2.33/1.01  fof(f43,plain,(
% 2.33/1.01    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK0(X0,X1,X2)) & r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.33/1.01    introduced(choice_axiom,[])).
% 2.33/1.01  
% 2.33/1.01  fof(f44,plain,(
% 2.33/1.01    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK0(X0,X1,X2)) & r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 2.33/1.01  
% 2.33/1.01  fof(f71,plain,(
% 2.33/1.01    ( ! [X2,X0,X3,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.01    inference(cnf_transformation,[],[f44])).
% 2.33/1.01  
% 2.33/1.01  fof(f3,axiom,(
% 2.33/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.33/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.01  
% 2.33/1.01  fof(f18,plain,(
% 2.33/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.33/1.01    inference(ennf_transformation,[],[f3])).
% 2.33/1.01  
% 2.33/1.01  fof(f19,plain,(
% 2.33/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.33/1.01    inference(flattening,[],[f18])).
% 2.33/1.01  
% 2.33/1.01  fof(f61,plain,(
% 2.33/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.33/1.01    inference(cnf_transformation,[],[f19])).
% 2.33/1.01  
% 2.33/1.01  fof(f2,axiom,(
% 2.33/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.33/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.01  
% 2.33/1.01  fof(f16,plain,(
% 2.33/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.33/1.01    inference(ennf_transformation,[],[f2])).
% 2.33/1.01  
% 2.33/1.01  fof(f17,plain,(
% 2.33/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.33/1.01    inference(flattening,[],[f16])).
% 2.33/1.01  
% 2.33/1.01  fof(f60,plain,(
% 2.33/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.33/1.01    inference(cnf_transformation,[],[f17])).
% 2.33/1.01  
% 2.33/1.01  fof(f4,axiom,(
% 2.33/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.33/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.01  
% 2.33/1.01  fof(f20,plain,(
% 2.33/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.33/1.01    inference(ennf_transformation,[],[f4])).
% 2.33/1.01  
% 2.33/1.01  fof(f62,plain,(
% 2.33/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.33/1.01    inference(cnf_transformation,[],[f20])).
% 2.33/1.01  
% 2.33/1.01  fof(f6,axiom,(
% 2.33/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.33/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.01  
% 2.33/1.01  fof(f22,plain,(
% 2.33/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.33/1.01    inference(ennf_transformation,[],[f6])).
% 2.33/1.01  
% 2.33/1.01  fof(f23,plain,(
% 2.33/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.33/1.01    inference(flattening,[],[f22])).
% 2.33/1.01  
% 2.33/1.01  fof(f64,plain,(
% 2.33/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.33/1.01    inference(cnf_transformation,[],[f23])).
% 2.33/1.01  
% 2.33/1.01  fof(f5,axiom,(
% 2.33/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.33/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.01  
% 2.33/1.01  fof(f21,plain,(
% 2.33/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.33/1.01    inference(ennf_transformation,[],[f5])).
% 2.33/1.01  
% 2.33/1.01  fof(f63,plain,(
% 2.33/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.33/1.01    inference(cnf_transformation,[],[f21])).
% 2.33/1.01  
% 2.33/1.01  fof(f95,plain,(
% 2.33/1.01    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | ~r1_tmap_1(sK2,sK1,sK3,sK5)),
% 2.33/1.01    inference(cnf_transformation,[],[f56])).
% 2.33/1.01  
% 2.33/1.01  fof(f93,plain,(
% 2.33/1.01    sK5 = sK6),
% 2.33/1.01    inference(cnf_transformation,[],[f56])).
% 2.33/1.01  
% 2.33/1.01  fof(f92,plain,(
% 2.33/1.01    m1_subset_1(sK6,u1_struct_0(sK4))),
% 2.33/1.01    inference(cnf_transformation,[],[f56])).
% 2.33/1.01  
% 2.33/1.01  fof(f77,plain,(
% 2.33/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.01    inference(cnf_transformation,[],[f47])).
% 2.33/1.01  
% 2.33/1.01  fof(f103,plain,(
% 2.33/1.01    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.01    inference(equality_resolution,[],[f77])).
% 2.33/1.01  
% 2.33/1.01  fof(f12,axiom,(
% 2.33/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.33/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.01  
% 2.33/1.01  fof(f33,plain,(
% 2.33/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/1.01    inference(ennf_transformation,[],[f12])).
% 2.33/1.01  
% 2.33/1.01  fof(f34,plain,(
% 2.33/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.01    inference(flattening,[],[f33])).
% 2.33/1.01  
% 2.33/1.01  fof(f76,plain,(
% 2.33/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.01    inference(cnf_transformation,[],[f34])).
% 2.33/1.01  
% 2.33/1.01  fof(f101,plain,(
% 2.33/1.01    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.01    inference(equality_resolution,[],[f76])).
% 2.33/1.01  
% 2.33/1.01  fof(f94,plain,(
% 2.33/1.01    r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | r1_tmap_1(sK2,sK1,sK3,sK5)),
% 2.33/1.01    inference(cnf_transformation,[],[f56])).
% 2.33/1.01  
% 2.33/1.01  fof(f11,axiom,(
% 2.33/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.33/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.01  
% 2.33/1.01  fof(f32,plain,(
% 2.33/1.01    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.33/1.01    inference(ennf_transformation,[],[f11])).
% 2.33/1.01  
% 2.33/1.01  fof(f75,plain,(
% 2.33/1.01    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.33/1.01    inference(cnf_transformation,[],[f32])).
% 2.33/1.01  
% 2.33/1.01  fof(f10,axiom,(
% 2.33/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.33/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.01  
% 2.33/1.01  fof(f30,plain,(
% 2.33/1.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.33/1.01    inference(ennf_transformation,[],[f10])).
% 2.33/1.01  
% 2.33/1.01  fof(f31,plain,(
% 2.33/1.01    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.33/1.01    inference(flattening,[],[f30])).
% 2.33/1.01  
% 2.33/1.01  fof(f45,plain,(
% 2.33/1.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.33/1.01    inference(nnf_transformation,[],[f31])).
% 2.33/1.01  
% 2.33/1.01  fof(f46,plain,(
% 2.33/1.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.33/1.01    inference(flattening,[],[f45])).
% 2.33/1.01  
% 2.33/1.01  fof(f72,plain,(
% 2.33/1.01    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.33/1.01    inference(cnf_transformation,[],[f46])).
% 2.33/1.01  
% 2.33/1.01  fof(f100,plain,(
% 2.33/1.01    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.33/1.01    inference(equality_resolution,[],[f72])).
% 2.33/1.01  
% 2.33/1.01  fof(f89,plain,(
% 2.33/1.01    v1_tsep_1(sK4,sK2)),
% 2.33/1.01    inference(cnf_transformation,[],[f56])).
% 2.33/1.01  
% 2.33/1.01  cnf(c_27,negated_conjecture,
% 2.33/1.01      ( m1_pre_topc(sK4,sK2) ),
% 2.33/1.01      inference(cnf_transformation,[],[f90]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_20,plain,
% 2.33/1.01      ( r1_tmap_1(X0,X1,X2,X3)
% 2.33/1.01      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.33/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.33/1.01      | ~ m1_connsp_2(X5,X0,X3)
% 2.33/1.01      | ~ m1_pre_topc(X4,X0)
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.33/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.33/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/1.01      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.33/1.01      | ~ v1_funct_1(X2)
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | ~ v2_pre_topc(X0)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | v2_struct_0(X4)
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | ~ l1_pre_topc(X0) ),
% 2.33/1.01      inference(cnf_transformation,[],[f102]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_31,negated_conjecture,
% 2.33/1.01      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 2.33/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_858,plain,
% 2.33/1.01      ( r1_tmap_1(X0,X1,X2,X3)
% 2.33/1.01      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.33/1.01      | ~ m1_connsp_2(X5,X0,X3)
% 2.33/1.01      | ~ m1_pre_topc(X4,X0)
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.33/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.33/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/1.01      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.33/1.01      | ~ v1_funct_1(X2)
% 2.33/1.01      | ~ v2_pre_topc(X0)
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | v2_struct_0(X4)
% 2.33/1.01      | ~ l1_pre_topc(X0)
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.33/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.33/1.01      | sK3 != X2 ),
% 2.33/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_859,plain,
% 2.33/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.33/1.01      | r1_tmap_1(X2,X1,sK3,X3)
% 2.33/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.33/1.01      | ~ m1_pre_topc(X0,X2)
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.33/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.33/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.33/1.01      | ~ v1_funct_1(sK3)
% 2.33/1.01      | ~ v2_pre_topc(X2)
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | v2_struct_0(X2)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | ~ l1_pre_topc(X2)
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.33/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.33/1.01      inference(unflattening,[status(thm)],[c_858]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_32,negated_conjecture,
% 2.33/1.01      ( v1_funct_1(sK3) ),
% 2.33/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_863,plain,
% 2.33/1.01      ( ~ r1_tarski(X4,u1_struct_0(X0))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.33/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.33/1.01      | ~ m1_pre_topc(X0,X2)
% 2.33/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.33/1.01      | r1_tmap_1(X2,X1,sK3,X3)
% 2.33/1.01      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.33/1.01      | ~ v2_pre_topc(X2)
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | v2_struct_0(X2)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | ~ l1_pre_topc(X2)
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.33/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.33/1.01      inference(global_propositional_subsumption,
% 2.33/1.01                [status(thm)],
% 2.33/1.01                [c_859,c_32]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_864,plain,
% 2.33/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.33/1.01      | r1_tmap_1(X2,X1,sK3,X3)
% 2.33/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.33/1.01      | ~ m1_pre_topc(X0,X2)
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.33/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.33/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | ~ v2_pre_topc(X2)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | v2_struct_0(X2)
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | ~ l1_pre_topc(X2)
% 2.33/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.33/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.33/1.01      inference(renaming,[status(thm)],[c_863]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_8,plain,
% 2.33/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.33/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/1.01      | m1_subset_1(X2,u1_struct_0(X1))
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | ~ l1_pre_topc(X1) ),
% 2.33/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_905,plain,
% 2.33/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.33/1.01      | r1_tmap_1(X2,X1,sK3,X3)
% 2.33/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.33/1.01      | ~ m1_pre_topc(X0,X2)
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.33/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.33/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | ~ v2_pre_topc(X2)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | v2_struct_0(X2)
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | ~ l1_pre_topc(X2)
% 2.33/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.33/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.33/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_864,c_8]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1015,plain,
% 2.33/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.33/1.01      | r1_tmap_1(X2,X1,sK3,X3)
% 2.33/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.33/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.33/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.33/1.01      | ~ v2_pre_topc(X2)
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | v2_struct_0(X2)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | ~ l1_pre_topc(X2)
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.33/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.33/1.01      | sK2 != X2
% 2.33/1.01      | sK4 != X0 ),
% 2.33/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_905]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1016,plain,
% 2.33/1.01      ( r1_tmap_1(sK2,X0,sK3,X1)
% 2.33/1.01      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.33/1.01      | ~ m1_connsp_2(X2,sK2,X1)
% 2.33/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.33/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.33/1.01      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 2.33/1.01      | ~ v2_pre_topc(X0)
% 2.33/1.01      | ~ v2_pre_topc(sK2)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | v2_struct_0(sK2)
% 2.33/1.01      | v2_struct_0(sK4)
% 2.33/1.01      | ~ l1_pre_topc(X0)
% 2.33/1.01      | ~ l1_pre_topc(sK2)
% 2.33/1.01      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.33/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.33/1.01      inference(unflattening,[status(thm)],[c_1015]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_35,negated_conjecture,
% 2.33/1.01      ( ~ v2_struct_0(sK2) ),
% 2.33/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_34,negated_conjecture,
% 2.33/1.01      ( v2_pre_topc(sK2) ),
% 2.33/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_33,negated_conjecture,
% 2.33/1.01      ( l1_pre_topc(sK2) ),
% 2.33/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_29,negated_conjecture,
% 2.33/1.01      ( ~ v2_struct_0(sK4) ),
% 2.33/1.01      inference(cnf_transformation,[],[f88]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1020,plain,
% 2.33/1.01      ( ~ l1_pre_topc(X0)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | r1_tmap_1(sK2,X0,sK3,X1)
% 2.33/1.01      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.33/1.01      | ~ m1_connsp_2(X2,sK2,X1)
% 2.33/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.33/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.33/1.01      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 2.33/1.01      | ~ v2_pre_topc(X0)
% 2.33/1.01      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.33/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.33/1.01      inference(global_propositional_subsumption,
% 2.33/1.01                [status(thm)],
% 2.33/1.01                [c_1016,c_35,c_34,c_33,c_29]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1021,plain,
% 2.33/1.01      ( r1_tmap_1(sK2,X0,sK3,X1)
% 2.33/1.01      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.33/1.01      | ~ m1_connsp_2(X2,sK2,X1)
% 2.33/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.33/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.33/1.01      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 2.33/1.01      | ~ v2_pre_topc(X0)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | ~ l1_pre_topc(X0)
% 2.33/1.01      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.33/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.33/1.01      inference(renaming,[status(thm)],[c_1020]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_37,negated_conjecture,
% 2.33/1.01      ( v2_pre_topc(sK1) ),
% 2.33/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1449,plain,
% 2.33/1.01      ( r1_tmap_1(sK2,X0,sK3,X1)
% 2.33/1.01      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.33/1.01      | ~ m1_connsp_2(X2,sK2,X1)
% 2.33/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.33/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.33/1.01      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | ~ l1_pre_topc(X0)
% 2.33/1.01      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.33/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.33/1.01      | sK1 != X0 ),
% 2.33/1.01      inference(resolution_lifted,[status(thm)],[c_1021,c_37]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1450,plain,
% 2.33/1.01      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 2.33/1.01      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.33/1.01      | ~ m1_connsp_2(X1,sK2,X0)
% 2.33/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.33/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.33/1.01      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 2.33/1.01      | v2_struct_0(sK1)
% 2.33/1.01      | ~ l1_pre_topc(sK1)
% 2.33/1.01      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.33/1.01      inference(unflattening,[status(thm)],[c_1449]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_38,negated_conjecture,
% 2.33/1.01      ( ~ v2_struct_0(sK1) ),
% 2.33/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_36,negated_conjecture,
% 2.33/1.01      ( l1_pre_topc(sK1) ),
% 2.33/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_30,negated_conjecture,
% 2.33/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 2.33/1.01      inference(cnf_transformation,[],[f87]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1454,plain,
% 2.33/1.01      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.33/1.01      | ~ m1_connsp_2(X1,sK2,X0)
% 2.33/1.01      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.33/1.01      | r1_tmap_1(sK2,sK1,sK3,X0)
% 2.33/1.01      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 2.33/1.01      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.33/1.01      inference(global_propositional_subsumption,
% 2.33/1.01                [status(thm)],
% 2.33/1.01                [c_1450,c_38,c_36,c_30]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1455,plain,
% 2.33/1.01      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 2.33/1.01      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.33/1.01      | ~ m1_connsp_2(X1,sK2,X0)
% 2.33/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.33/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 2.33/1.01      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.33/1.01      inference(renaming,[status(thm)],[c_1454]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_3388,plain,
% 2.33/1.01      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 2.33/1.01      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.33/1.01      | ~ m1_connsp_2(X1,sK2,X0)
% 2.33/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.33/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ r1_tarski(X1,u1_struct_0(sK4)) ),
% 2.33/1.01      inference(equality_resolution_simp,[status(thm)],[c_1455]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_6043,plain,
% 2.33/1.01      ( r1_tmap_1(sK2,sK1,sK3,sK6)
% 2.33/1.01      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 2.33/1.01      | ~ m1_connsp_2(X0,sK2,sK6)
% 2.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.33/1.01      | ~ r1_tarski(X0,u1_struct_0(sK4)) ),
% 2.33/1.01      inference(instantiation,[status(thm)],[c_3388]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_6956,plain,
% 2.33/1.01      ( r1_tmap_1(sK2,sK1,sK3,sK6)
% 2.33/1.01      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 2.33/1.01      | ~ m1_connsp_2(u1_struct_0(sK4),sK2,sK6)
% 2.33/1.01      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.33/1.01      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 2.33/1.01      inference(instantiation,[status(thm)],[c_6043]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1,plain,
% 2.33/1.01      ( r1_tarski(X0,X0) ),
% 2.33/1.01      inference(cnf_transformation,[],[f96]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_6622,plain,
% 2.33/1.01      ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 2.33/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_10,plain,
% 2.33/1.01      ( m1_connsp_2(X0,X1,X2)
% 2.33/1.01      | ~ v3_pre_topc(X3,X1)
% 2.33/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.33/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.01      | ~ r2_hidden(X2,X3)
% 2.33/1.01      | ~ r1_tarski(X3,X0)
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | ~ l1_pre_topc(X1) ),
% 2.33/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1566,plain,
% 2.33/1.01      ( m1_connsp_2(X0,X1,X2)
% 2.33/1.01      | ~ v3_pre_topc(X3,X1)
% 2.33/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.33/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.01      | ~ r2_hidden(X2,X3)
% 2.33/1.01      | ~ r1_tarski(X3,X0)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | sK2 != X1 ),
% 2.33/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_34]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1567,plain,
% 2.33/1.01      ( m1_connsp_2(X0,sK2,X1)
% 2.33/1.01      | ~ v3_pre_topc(X2,sK2)
% 2.33/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ r2_hidden(X1,X2)
% 2.33/1.01      | ~ r1_tarski(X2,X0)
% 2.33/1.01      | v2_struct_0(sK2)
% 2.33/1.01      | ~ l1_pre_topc(sK2) ),
% 2.33/1.01      inference(unflattening,[status(thm)],[c_1566]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1571,plain,
% 2.33/1.01      ( m1_connsp_2(X0,sK2,X1)
% 2.33/1.01      | ~ v3_pre_topc(X2,sK2)
% 2.33/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ r2_hidden(X1,X2)
% 2.33/1.01      | ~ r1_tarski(X2,X0) ),
% 2.33/1.01      inference(global_propositional_subsumption,
% 2.33/1.01                [status(thm)],
% 2.33/1.01                [c_1567,c_35,c_33]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_4,plain,
% 2.33/1.01      ( m1_subset_1(X0,X1)
% 2.33/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.33/1.01      | ~ r2_hidden(X0,X2) ),
% 2.33/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1591,plain,
% 2.33/1.01      ( m1_connsp_2(X0,sK2,X1)
% 2.33/1.01      | ~ v3_pre_topc(X2,sK2)
% 2.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ r2_hidden(X1,X2)
% 2.33/1.01      | ~ r1_tarski(X2,X0) ),
% 2.33/1.01      inference(forward_subsumption_resolution,
% 2.33/1.01                [status(thm)],
% 2.33/1.01                [c_1571,c_4]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_6048,plain,
% 2.33/1.01      ( m1_connsp_2(X0,sK2,X1)
% 2.33/1.01      | ~ v3_pre_topc(u1_struct_0(sK4),sK2)
% 2.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ r2_hidden(X1,u1_struct_0(sK4))
% 2.33/1.01      | ~ r1_tarski(u1_struct_0(sK4),X0) ),
% 2.33/1.01      inference(instantiation,[status(thm)],[c_1591]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_6451,plain,
% 2.33/1.01      ( m1_connsp_2(X0,sK2,sK6)
% 2.33/1.01      | ~ v3_pre_topc(u1_struct_0(sK4),sK2)
% 2.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ r2_hidden(sK6,u1_struct_0(sK4))
% 2.33/1.01      | ~ r1_tarski(u1_struct_0(sK4),X0) ),
% 2.33/1.01      inference(instantiation,[status(thm)],[c_6048]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_6621,plain,
% 2.33/1.01      ( m1_connsp_2(u1_struct_0(sK4),sK2,sK6)
% 2.33/1.01      | ~ v3_pre_topc(u1_struct_0(sK4),sK2)
% 2.33/1.01      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ r2_hidden(sK6,u1_struct_0(sK4))
% 2.33/1.01      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 2.33/1.01      inference(instantiation,[status(thm)],[c_6451]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_3,plain,
% 2.33/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.33/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_5,plain,
% 2.33/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.33/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_7,plain,
% 2.33/1.01      ( v2_struct_0(X0)
% 2.33/1.01      | ~ l1_struct_0(X0)
% 2.33/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.33/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_513,plain,
% 2.33/1.01      ( v2_struct_0(X0)
% 2.33/1.01      | ~ l1_pre_topc(X0)
% 2.33/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.33/1.01      inference(resolution,[status(thm)],[c_5,c_7]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_6,plain,
% 2.33/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.33/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1004,plain,
% 2.33/1.01      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X0 | sK4 != X1 ),
% 2.33/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_27]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1005,plain,
% 2.33/1.01      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK4) ),
% 2.33/1.01      inference(unflattening,[status(thm)],[c_1004]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1007,plain,
% 2.33/1.01      ( l1_pre_topc(sK4) ),
% 2.33/1.01      inference(global_propositional_subsumption,
% 2.33/1.01                [status(thm)],
% 2.33/1.01                [c_1005,c_33]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1866,plain,
% 2.33/1.01      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK4 != X0 ),
% 2.33/1.01      inference(resolution_lifted,[status(thm)],[c_513,c_1007]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1867,plain,
% 2.33/1.01      ( v2_struct_0(sK4) | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 2.33/1.01      inference(unflattening,[status(thm)],[c_1866]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1869,plain,
% 2.33/1.01      ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 2.33/1.01      inference(global_propositional_subsumption,
% 2.33/1.01                [status(thm)],
% 2.33/1.01                [c_1867,c_29]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1907,plain,
% 2.33/1.01      ( ~ m1_subset_1(X0,X1)
% 2.33/1.01      | r2_hidden(X0,X1)
% 2.33/1.01      | u1_struct_0(sK4) != X1 ),
% 2.33/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_1869]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1908,plain,
% 2.33/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.33/1.01      | r2_hidden(X0,u1_struct_0(sK4)) ),
% 2.33/1.01      inference(unflattening,[status(thm)],[c_1907]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_6065,plain,
% 2.33/1.01      ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.33/1.01      | r2_hidden(sK6,u1_struct_0(sK4)) ),
% 2.33/1.01      inference(instantiation,[status(thm)],[c_1908]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_22,negated_conjecture,
% 2.33/1.01      ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
% 2.33/1.01      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 2.33/1.01      inference(cnf_transformation,[],[f95]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_5739,plain,
% 2.33/1.01      ( r1_tmap_1(sK2,sK1,sK3,sK5) != iProver_top
% 2.33/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
% 2.33/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_24,negated_conjecture,
% 2.33/1.01      ( sK5 = sK6 ),
% 2.33/1.01      inference(cnf_transformation,[],[f93]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_5791,plain,
% 2.33/1.01      ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
% 2.33/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
% 2.33/1.01      inference(light_normalisation,[status(thm)],[c_5739,c_24]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_25,negated_conjecture,
% 2.33/1.01      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.33/1.01      inference(cnf_transformation,[],[f92]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_52,plain,
% 2.33/1.01      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 2.33/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_21,plain,
% 2.33/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.33/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.33/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.33/1.01      | ~ m1_connsp_2(X5,X0,X3)
% 2.33/1.01      | ~ m1_pre_topc(X4,X0)
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.33/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.33/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/1.01      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.33/1.01      | ~ v1_funct_1(X2)
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | ~ v2_pre_topc(X0)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | v2_struct_0(X4)
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | ~ l1_pre_topc(X0) ),
% 2.33/1.01      inference(cnf_transformation,[],[f103]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_19,plain,
% 2.33/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.33/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.33/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.33/1.01      | ~ m1_pre_topc(X4,X0)
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.33/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.33/1.01      | ~ v1_funct_1(X2)
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | ~ v2_pre_topc(X0)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | v2_struct_0(X4)
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | ~ l1_pre_topc(X0) ),
% 2.33/1.01      inference(cnf_transformation,[],[f101]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_206,plain,
% 2.33/1.01      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.33/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.33/1.01      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.33/1.01      | ~ m1_pre_topc(X4,X0)
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.33/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.33/1.01      | ~ v1_funct_1(X2)
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | ~ v2_pre_topc(X0)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | v2_struct_0(X4)
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | ~ l1_pre_topc(X0) ),
% 2.33/1.01      inference(global_propositional_subsumption,
% 2.33/1.01                [status(thm)],
% 2.33/1.01                [c_21,c_19]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_207,plain,
% 2.33/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.33/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.33/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.33/1.01      | ~ m1_pre_topc(X4,X0)
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.33/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.33/1.01      | ~ v1_funct_1(X2)
% 2.33/1.01      | ~ v2_pre_topc(X0)
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | v2_struct_0(X4)
% 2.33/1.01      | ~ l1_pre_topc(X0)
% 2.33/1.01      | ~ l1_pre_topc(X1) ),
% 2.33/1.01      inference(renaming,[status(thm)],[c_206]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_801,plain,
% 2.33/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.33/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.33/1.01      | ~ m1_pre_topc(X4,X0)
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.33/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.33/1.01      | ~ v1_funct_1(X2)
% 2.33/1.01      | ~ v2_pre_topc(X0)
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | v2_struct_0(X4)
% 2.33/1.01      | ~ l1_pre_topc(X0)
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.33/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.33/1.01      | sK3 != X2 ),
% 2.33/1.01      inference(resolution_lifted,[status(thm)],[c_207,c_31]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_802,plain,
% 2.33/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.33/1.01      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.33/1.01      | ~ m1_pre_topc(X0,X2)
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.33/1.01      | ~ v1_funct_1(sK3)
% 2.33/1.01      | ~ v2_pre_topc(X2)
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | v2_struct_0(X2)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | ~ l1_pre_topc(X2)
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.33/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.33/1.01      inference(unflattening,[status(thm)],[c_801]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_806,plain,
% 2.33/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.33/1.01      | ~ m1_pre_topc(X0,X2)
% 2.33/1.01      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.33/1.01      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.33/1.01      | ~ v2_pre_topc(X2)
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | v2_struct_0(X2)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | ~ l1_pre_topc(X2)
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.33/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.33/1.01      inference(global_propositional_subsumption,
% 2.33/1.01                [status(thm)],
% 2.33/1.01                [c_802,c_32]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_807,plain,
% 2.33/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.33/1.01      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.33/1.01      | ~ m1_pre_topc(X0,X2)
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | ~ v2_pre_topc(X2)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | v2_struct_0(X2)
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | ~ l1_pre_topc(X2)
% 2.33/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.33/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.33/1.01      inference(renaming,[status(thm)],[c_806]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_842,plain,
% 2.33/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.33/1.01      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.33/1.01      | ~ m1_pre_topc(X0,X2)
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | ~ v2_pre_topc(X2)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | v2_struct_0(X2)
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | ~ l1_pre_topc(X2)
% 2.33/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.33/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.33/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_807,c_8]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1063,plain,
% 2.33/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.33/1.01      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.33/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.33/1.01      | ~ v2_pre_topc(X2)
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | v2_struct_0(X2)
% 2.33/1.01      | v2_struct_0(X1)
% 2.33/1.01      | ~ l1_pre_topc(X2)
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.33/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.33/1.01      | sK2 != X2
% 2.33/1.01      | sK4 != X0 ),
% 2.33/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_842]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1064,plain,
% 2.33/1.01      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 2.33/1.01      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.33/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.33/1.01      | ~ v2_pre_topc(X0)
% 2.33/1.01      | ~ v2_pre_topc(sK2)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | v2_struct_0(sK2)
% 2.33/1.01      | v2_struct_0(sK4)
% 2.33/1.01      | ~ l1_pre_topc(X0)
% 2.33/1.01      | ~ l1_pre_topc(sK2)
% 2.33/1.01      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.33/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.33/1.01      inference(unflattening,[status(thm)],[c_1063]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1068,plain,
% 2.33/1.01      ( ~ l1_pre_topc(X0)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | ~ r1_tmap_1(sK2,X0,sK3,X1)
% 2.33/1.01      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.33/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.33/1.01      | ~ v2_pre_topc(X0)
% 2.33/1.01      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.33/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.33/1.01      inference(global_propositional_subsumption,
% 2.33/1.01                [status(thm)],
% 2.33/1.01                [c_1064,c_35,c_34,c_33,c_29]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1069,plain,
% 2.33/1.01      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 2.33/1.01      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.33/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.33/1.01      | ~ v2_pre_topc(X0)
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | ~ l1_pre_topc(X0)
% 2.33/1.01      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.33/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.33/1.01      inference(renaming,[status(thm)],[c_1068]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1425,plain,
% 2.33/1.01      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 2.33/1.01      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.33/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.33/1.01      | v2_struct_0(X0)
% 2.33/1.01      | ~ l1_pre_topc(X0)
% 2.33/1.01      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.33/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.33/1.01      | sK1 != X0 ),
% 2.33/1.01      inference(resolution_lifted,[status(thm)],[c_1069,c_37]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1426,plain,
% 2.33/1.01      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 2.33/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.33/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.33/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.33/1.01      | v2_struct_0(sK1)
% 2.33/1.01      | ~ l1_pre_topc(sK1)
% 2.33/1.01      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.33/1.01      inference(unflattening,[status(thm)],[c_1425]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1430,plain,
% 2.33/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.33/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.33/1.01      | ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 2.33/1.01      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.33/1.01      inference(global_propositional_subsumption,
% 2.33/1.01                [status(thm)],
% 2.33/1.01                [c_1426,c_38,c_36,c_30]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_1431,plain,
% 2.33/1.01      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 2.33/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.33/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.33/1.01      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.33/1.01      inference(renaming,[status(thm)],[c_1430]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_3392,plain,
% 2.33/1.01      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 2.33/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.33/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 2.33/1.01      inference(equality_resolution_simp,[status(thm)],[c_1431]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_6040,plain,
% 2.33/1.01      ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
% 2.33/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 2.33/1.01      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.33/1.01      inference(instantiation,[status(thm)],[c_3392]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_6041,plain,
% 2.33/1.01      ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
% 2.33/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top
% 2.33/1.01      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 2.33/1.01      inference(predicate_to_equality,[status(thm)],[c_6040]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_6054,plain,
% 2.33/1.01      ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top ),
% 2.33/1.01      inference(global_propositional_subsumption,
% 2.33/1.01                [status(thm)],
% 2.33/1.01                [c_5791,c_52,c_6041]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_6056,plain,
% 2.33/1.01      ( ~ r1_tmap_1(sK2,sK1,sK3,sK6) ),
% 2.33/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_6054]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_23,negated_conjecture,
% 2.33/1.01      ( r1_tmap_1(sK2,sK1,sK3,sK5)
% 2.33/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 2.33/1.01      inference(cnf_transformation,[],[f94]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_5738,plain,
% 2.33/1.01      ( r1_tmap_1(sK2,sK1,sK3,sK5) = iProver_top
% 2.33/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
% 2.33/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_5780,plain,
% 2.33/1.01      ( r1_tmap_1(sK2,sK1,sK3,sK6) = iProver_top
% 2.33/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
% 2.33/1.01      inference(light_normalisation,[status(thm)],[c_5738,c_24]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_5940,plain,
% 2.33/1.01      ( r1_tmap_1(sK2,sK1,sK3,sK6)
% 2.33/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 2.33/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_5780]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_18,plain,
% 2.33/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.33/1.01      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.01      | ~ l1_pre_topc(X1) ),
% 2.33/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_975,plain,
% 2.33/1.01      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | sK2 != X1
% 2.33/1.01      | sK4 != X0 ),
% 2.33/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_976,plain,
% 2.33/1.01      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.01      | ~ l1_pre_topc(sK2) ),
% 2.33/1.01      inference(unflattening,[status(thm)],[c_975]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_17,plain,
% 2.33/1.01      ( ~ v1_tsep_1(X0,X1)
% 2.33/1.01      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.33/1.01      | ~ m1_pre_topc(X0,X1)
% 2.33/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | ~ l1_pre_topc(X1) ),
% 2.33/1.01      inference(cnf_transformation,[],[f100]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_214,plain,
% 2.33/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.33/1.01      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.33/1.01      | ~ v1_tsep_1(X0,X1)
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | ~ l1_pre_topc(X1) ),
% 2.33/1.01      inference(global_propositional_subsumption,
% 2.33/1.01                [status(thm)],
% 2.33/1.01                [c_17,c_18]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_215,plain,
% 2.33/1.01      ( ~ v1_tsep_1(X0,X1)
% 2.33/1.01      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.33/1.01      | ~ m1_pre_topc(X0,X1)
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | ~ l1_pre_topc(X1) ),
% 2.33/1.01      inference(renaming,[status(thm)],[c_214]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_28,negated_conjecture,
% 2.33/1.01      ( v1_tsep_1(sK4,sK2) ),
% 2.33/1.01      inference(cnf_transformation,[],[f89]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_554,plain,
% 2.33/1.01      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.33/1.01      | ~ m1_pre_topc(X0,X1)
% 2.33/1.01      | ~ v2_pre_topc(X1)
% 2.33/1.01      | ~ l1_pre_topc(X1)
% 2.33/1.01      | sK2 != X1
% 2.33/1.01      | sK4 != X0 ),
% 2.33/1.01      inference(resolution_lifted,[status(thm)],[c_215,c_28]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(c_555,plain,
% 2.33/1.01      ( v3_pre_topc(u1_struct_0(sK4),sK2)
% 2.33/1.01      | ~ m1_pre_topc(sK4,sK2)
% 2.33/1.01      | ~ v2_pre_topc(sK2)
% 2.33/1.01      | ~ l1_pre_topc(sK2) ),
% 2.33/1.01      inference(unflattening,[status(thm)],[c_554]) ).
% 2.33/1.01  
% 2.33/1.01  cnf(contradiction,plain,
% 2.33/1.01      ( $false ),
% 2.33/1.01      inference(minisat,
% 2.33/1.01                [status(thm)],
% 2.33/1.01                [c_6956,c_6622,c_6621,c_6065,c_6056,c_5940,c_976,c_555,
% 2.33/1.01                 c_25,c_27,c_33,c_34]) ).
% 2.33/1.01  
% 2.33/1.01  
% 2.33/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.33/1.01  
% 2.33/1.01  ------                               Statistics
% 2.33/1.01  
% 2.33/1.01  ------ General
% 2.33/1.01  
% 2.33/1.01  abstr_ref_over_cycles:                  0
% 2.33/1.01  abstr_ref_under_cycles:                 0
% 2.33/1.01  gc_basic_clause_elim:                   0
% 2.33/1.01  forced_gc_time:                         0
% 2.33/1.01  parsing_time:                           0.019
% 2.33/1.01  unif_index_cands_time:                  0.
% 2.33/1.01  unif_index_add_time:                    0.
% 2.33/1.01  orderings_time:                         0.
% 2.33/1.01  out_proof_time:                         0.014
% 2.33/1.01  total_time:                             0.194
% 2.33/1.01  num_of_symbols:                         59
% 2.33/1.01  num_of_terms:                           2638
% 2.33/1.01  
% 2.33/1.01  ------ Preprocessing
% 2.33/1.01  
% 2.33/1.01  num_of_splits:                          2
% 2.33/1.01  num_of_split_atoms:                     2
% 2.33/1.01  num_of_reused_defs:                     0
% 2.33/1.01  num_eq_ax_congr_red:                    19
% 2.33/1.01  num_of_sem_filtered_clauses:            1
% 2.33/1.01  num_of_subtypes:                        0
% 2.33/1.01  monotx_restored_types:                  0
% 2.33/1.01  sat_num_of_epr_types:                   0
% 2.33/1.01  sat_num_of_non_cyclic_types:            0
% 2.33/1.01  sat_guarded_non_collapsed_types:        0
% 2.33/1.01  num_pure_diseq_elim:                    0
% 2.33/1.01  simp_replaced_by:                       0
% 2.33/1.01  res_preprocessed:                       161
% 2.33/1.01  prep_upred:                             0
% 2.33/1.01  prep_unflattend:                        181
% 2.33/1.01  smt_new_axioms:                         0
% 2.33/1.01  pred_elim_cands:                        6
% 2.33/1.01  pred_elim:                              9
% 2.33/1.01  pred_elim_cl:                           6
% 2.33/1.01  pred_elim_cycles:                       19
% 2.33/1.01  merged_defs:                            8
% 2.33/1.01  merged_defs_ncl:                        0
% 2.33/1.01  bin_hyper_res:                          8
% 2.33/1.01  prep_cycles:                            4
% 2.33/1.01  pred_elim_time:                         0.09
% 2.33/1.01  splitting_time:                         0.
% 2.33/1.01  sem_filter_time:                        0.
% 2.33/1.01  monotx_time:                            0.
% 2.33/1.01  subtype_inf_time:                       0.
% 2.33/1.01  
% 2.33/1.01  ------ Problem properties
% 2.33/1.01  
% 2.33/1.01  clauses:                                33
% 2.33/1.01  conjectures:                            6
% 2.33/1.01  epr:                                    3
% 2.33/1.01  horn:                                   32
% 2.33/1.01  ground:                                 10
% 2.33/1.01  unary:                                  7
% 2.33/1.01  binary:                                 6
% 2.33/1.01  lits:                                   93
% 2.33/1.01  lits_eq:                                4
% 2.33/1.01  fd_pure:                                0
% 2.33/1.01  fd_pseudo:                              0
% 2.33/1.01  fd_cond:                                0
% 2.33/1.01  fd_pseudo_cond:                         1
% 2.33/1.01  ac_symbols:                             0
% 2.33/1.01  
% 2.33/1.01  ------ Propositional Solver
% 2.33/1.01  
% 2.33/1.01  prop_solver_calls:                      26
% 2.33/1.01  prop_fast_solver_calls:                 2323
% 2.33/1.01  smt_solver_calls:                       0
% 2.33/1.01  smt_fast_solver_calls:                  0
% 2.33/1.01  prop_num_of_clauses:                    1164
% 2.33/1.01  prop_preprocess_simplified:             5733
% 2.33/1.01  prop_fo_subsumed:                       95
% 2.33/1.01  prop_solver_time:                       0.
% 2.33/1.01  smt_solver_time:                        0.
% 2.33/1.01  smt_fast_solver_time:                   0.
% 2.33/1.01  prop_fast_solver_time:                  0.
% 2.33/1.01  prop_unsat_core_time:                   0.
% 2.33/1.01  
% 2.33/1.01  ------ QBF
% 2.33/1.01  
% 2.33/1.01  qbf_q_res:                              0
% 2.33/1.01  qbf_num_tautologies:                    0
% 2.33/1.01  qbf_prep_cycles:                        0
% 2.33/1.01  
% 2.33/1.01  ------ BMC1
% 2.33/1.01  
% 2.33/1.01  bmc1_current_bound:                     -1
% 2.33/1.01  bmc1_last_solved_bound:                 -1
% 2.33/1.01  bmc1_unsat_core_size:                   -1
% 2.33/1.01  bmc1_unsat_core_parents_size:           -1
% 2.33/1.01  bmc1_merge_next_fun:                    0
% 2.33/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.33/1.01  
% 2.33/1.01  ------ Instantiation
% 2.33/1.01  
% 2.33/1.01  inst_num_of_clauses:                    204
% 2.33/1.01  inst_num_in_passive:                    54
% 2.33/1.01  inst_num_in_active:                     136
% 2.33/1.01  inst_num_in_unprocessed:                13
% 2.33/1.01  inst_num_of_loops:                      143
% 2.33/1.01  inst_num_of_learning_restarts:          0
% 2.33/1.01  inst_num_moves_active_passive:          4
% 2.33/1.01  inst_lit_activity:                      0
% 2.33/1.01  inst_lit_activity_moves:                0
% 2.33/1.01  inst_num_tautologies:                   0
% 2.33/1.01  inst_num_prop_implied:                  0
% 2.33/1.01  inst_num_existing_simplified:           0
% 2.33/1.01  inst_num_eq_res_simplified:             0
% 2.33/1.01  inst_num_child_elim:                    0
% 2.33/1.01  inst_num_of_dismatching_blockings:      16
% 2.33/1.01  inst_num_of_non_proper_insts:           167
% 2.33/1.01  inst_num_of_duplicates:                 0
% 2.33/1.01  inst_inst_num_from_inst_to_res:         0
% 2.33/1.01  inst_dismatching_checking_time:         0.
% 2.33/1.01  
% 2.33/1.01  ------ Resolution
% 2.33/1.01  
% 2.33/1.01  res_num_of_clauses:                     0
% 2.33/1.01  res_num_in_passive:                     0
% 2.33/1.01  res_num_in_active:                      0
% 2.33/1.01  res_num_of_loops:                       165
% 2.33/1.01  res_forward_subset_subsumed:            28
% 2.33/1.01  res_backward_subset_subsumed:           0
% 2.33/1.01  res_forward_subsumed:                   0
% 2.33/1.01  res_backward_subsumed:                  0
% 2.33/1.01  res_forward_subsumption_resolution:     26
% 2.33/1.01  res_backward_subsumption_resolution:    0
% 2.33/1.01  res_clause_to_clause_subsumption:       623
% 2.33/1.01  res_orphan_elimination:                 0
% 2.33/1.01  res_tautology_del:                      42
% 2.33/1.01  res_num_eq_res_simplified:              2
% 2.33/1.01  res_num_sel_changes:                    0
% 2.33/1.01  res_moves_from_active_to_pass:          0
% 2.33/1.01  
% 2.33/1.01  ------ Superposition
% 2.33/1.01  
% 2.33/1.01  sup_time_total:                         0.
% 2.33/1.01  sup_time_generating:                    0.
% 2.33/1.01  sup_time_sim_full:                      0.
% 2.33/1.01  sup_time_sim_immed:                     0.
% 2.33/1.01  
% 2.33/1.01  sup_num_of_clauses:                     40
% 2.33/1.01  sup_num_in_active:                      28
% 2.33/1.01  sup_num_in_passive:                     12
% 2.33/1.01  sup_num_of_loops:                       28
% 2.33/1.01  sup_fw_superposition:                   7
% 2.33/1.01  sup_bw_superposition:                   2
% 2.33/1.01  sup_immediate_simplified:               0
% 2.33/1.01  sup_given_eliminated:                   0
% 2.33/1.01  comparisons_done:                       0
% 2.33/1.01  comparisons_avoided:                    0
% 2.33/1.01  
% 2.33/1.01  ------ Simplifications
% 2.33/1.01  
% 2.33/1.01  
% 2.33/1.01  sim_fw_subset_subsumed:                 0
% 2.33/1.01  sim_bw_subset_subsumed:                 0
% 2.33/1.01  sim_fw_subsumed:                        0
% 2.33/1.01  sim_bw_subsumed:                        0
% 2.33/1.01  sim_fw_subsumption_res:                 0
% 2.33/1.01  sim_bw_subsumption_res:                 0
% 2.33/1.01  sim_tautology_del:                      1
% 2.33/1.01  sim_eq_tautology_del:                   1
% 2.33/1.01  sim_eq_res_simp:                        0
% 2.33/1.01  sim_fw_demodulated:                     0
% 2.33/1.01  sim_bw_demodulated:                     0
% 2.33/1.01  sim_light_normalised:                   3
% 2.33/1.01  sim_joinable_taut:                      0
% 2.33/1.01  sim_joinable_simp:                      0
% 2.33/1.01  sim_ac_normalised:                      0
% 2.33/1.01  sim_smt_subsumption:                    0
% 2.33/1.01  
%------------------------------------------------------------------------------
