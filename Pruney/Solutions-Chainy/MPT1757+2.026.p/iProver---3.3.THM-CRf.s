%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:46 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :  207 (1363 expanded)
%              Number of clauses        :  121 ( 264 expanded)
%              Number of leaves         :   21 ( 512 expanded)
%              Depth                    :   42
%              Number of atoms          : 1437 (20688 expanded)
%              Number of equality atoms :  237 (1597 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

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
    inference(ennf_transformation,[],[f16])).

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
    inference(nnf_transformation,[],[f42])).

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
    inference(flattening,[],[f47])).

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f55,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f48,f54,f53,f52,f51,f50,f49])).

fof(f85,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f79,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f55])).

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
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f95,plain,(
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

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f63,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

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
    inference(nnf_transformation,[],[f32])).

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
    inference(cnf_transformation,[],[f44])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f77,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f83,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f75,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f76,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f55])).

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
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,(
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
    inference(ennf_transformation,[],[f13])).

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
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_12,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1499,plain,
    ( m1_pre_topc(X0_53,X0_53)
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2082,plain,
    ( m1_pre_topc(X0_53,X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1499])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1491,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2089,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1491])).

cnf(c_13,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1498,plain,
    ( r1_tarski(u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_pre_topc(X1_53,X2_53)
    | ~ m1_pre_topc(X0_53,X1_53)
    | ~ v2_pre_topc(X2_53)
    | ~ l1_pre_topc(X2_53) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2083,plain,
    ( r1_tarski(u1_struct_0(X0_53),u1_struct_0(X1_53)) = iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X2_53) != iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1498])).

cnf(c_3032,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_53)) = iProver_top
    | m1_pre_topc(X0_53,sK1) != iProver_top
    | m1_pre_topc(sK3,X0_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2089,c_2083])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_39,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_40,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3104,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_53)) = iProver_top
    | m1_pre_topc(X0_53,sK1) != iProver_top
    | m1_pre_topc(sK3,X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3032,c_39,c_40])).

cnf(c_19,negated_conjecture,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1495,negated_conjecture,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2086,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1495])).

cnf(c_20,negated_conjecture,
    ( sK4 = sK5 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1494,negated_conjecture,
    ( sK4 = sK5 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2144,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2086,c_1494])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_16,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
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

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_7,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_10,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_193,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_11])).

cnf(c_194,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_193])).

cnf(c_24,negated_conjecture,
    ( v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_488,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_194,c_24])).

cnf(c_489,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_491,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_30,c_29,c_23])).

cnf(c_501,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK3) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_491])).

cnf(c_502,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_506,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_connsp_2(u1_struct_0(sK3),sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_502,c_31,c_30,c_29])).

cnf(c_507,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_506])).

cnf(c_1,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_520,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,u1_struct_0(sK3)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_507,c_1])).

cnf(c_547,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(X2)
    | X0 != X1
    | u1_struct_0(sK3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_520])).

cnf(c_548,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_632,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X6,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
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
    | X6 != X3
    | u1_struct_0(sK3) != X5
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_548])).

cnf(c_633,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
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
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_637,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_633,c_31,c_30,c_29])).

cnf(c_638,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_637])).

cnf(c_531,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | v1_xboole_0(X1)
    | X2 != X0
    | X4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_532,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_673,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_638,c_532])).

cnf(c_925,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
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
    inference(resolution_lifted,[status(thm)],[c_27,c_673])).

cnf(c_926,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
    | r1_tmap_1(sK1,X1,sK2,X2)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_925])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_930,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | r1_tmap_1(sK1,X1,sK2,X2)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_926,c_28])).

cnf(c_931,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
    | r1_tmap_1(sK1,X1,sK2,X2)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_930])).

cnf(c_1479,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k2_tmap_1(sK1,X1_53,sK2,X0_53),X0_54)
    | r1_tmap_1(sK1,X1_53,sK2,X0_54)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_53))
    | ~ m1_pre_topc(X0_53,sK1)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1_53))))
    | ~ v2_pre_topc(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | ~ l1_pre_topc(X1_53)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1_53) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_931])).

cnf(c_1503,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k2_tmap_1(sK1,X1_53,sK2,X0_53),X0_54)
    | r1_tmap_1(sK1,X1_53,sK2,X0_54)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_53))
    | ~ m1_pre_topc(X0_53,sK1)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1_53))))
    | ~ v2_pre_topc(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | ~ l1_pre_topc(X1_53)
    | u1_struct_0(X1_53) != u1_struct_0(sK0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1479])).

cnf(c_2102,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK0)
    | r1_tmap_1(X1_53,X0_53,k2_tmap_1(sK1,X0_53,sK2,X1_53),X0_54) != iProver_top
    | r1_tmap_1(sK1,X0_53,sK2,X0_54) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X1_53,sK1) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_53)))) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1503])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_44,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_46,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1504,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK3))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1479])).

cnf(c_1548,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1504])).

cnf(c_1549,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK0)
    | r1_tmap_1(X1_53,X0_53,k2_tmap_1(sK1,X0_53,sK2,X1_53),X0_54) != iProver_top
    | r1_tmap_1(sK1,X0_53,sK2,X0_54) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X1_53,sK1) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_53)))) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1503])).

cnf(c_1500,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X1_53)))
    | ~ l1_pre_topc(X1_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2327,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1500])).

cnf(c_2328,plain,
    ( m1_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2327])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_447,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_2,c_4])).

cnf(c_1482,plain,
    ( v2_struct_0(X0_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v1_xboole_0(u1_struct_0(X0_53)) ),
    inference(subtyping,[status(esa)],[c_447])).

cnf(c_2498,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1482])).

cnf(c_2499,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2498])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1502,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2079,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1502])).

cnf(c_2518,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2089,c_2079])).

cnf(c_2768,plain,
    ( l1_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X1_53,sK1) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X1_53)) != iProver_top
    | r1_tmap_1(sK1,X0_53,sK2,X0_54) = iProver_top
    | r1_tmap_1(X1_53,X0_53,k2_tmap_1(sK1,X0_53,sK2,X1_53),X0_54) != iProver_top
    | u1_struct_0(X0_53) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2102,c_40,c_44,c_46,c_1548,c_1549,c_2328,c_2499,c_2518])).

cnf(c_2769,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK0)
    | r1_tmap_1(X1_53,X0_53,k2_tmap_1(sK1,X0_53,sK2,X1_53),X0_54) != iProver_top
    | r1_tmap_1(sK1,X0_53,sK2,X0_54) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X1_53,sK1) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_53)))) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2768])).

cnf(c_2786,plain,
    ( r1_tmap_1(X0_53,sK0,k2_tmap_1(sK1,sK0,sK2,X0_53),X0_54) != iProver_top
    | r1_tmap_1(sK1,sK0,sK2,X0_54) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(X0_53,sK1) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2769])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_35,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_36,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_37,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2854,plain,
    ( r1_tmap_1(X0_53,sK0,k2_tmap_1(sK1,sK0,sK2,X0_53),X0_54) != iProver_top
    | r1_tmap_1(sK1,sK0,sK2,X0_54) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(X0_53,sK1) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2786,c_35,c_36,c_37,c_43])).

cnf(c_2867,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2144,c_2854])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_48,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2870,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2867,c_44,c_46,c_48])).

cnf(c_2871,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2870])).

cnf(c_3114,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3104,c_2871])).

cnf(c_38,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1496,negated_conjecture,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2085,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1496])).

cnf(c_2161,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2085,c_1494])).

cnf(c_1506,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_2319,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_2528,plain,
    ( u1_struct_0(X0_53) = u1_struct_0(X0_53) ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_2706,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2528])).

cnf(c_17,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
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
    inference(cnf_transformation,[],[f96])).

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
    inference(cnf_transformation,[],[f94])).

cnf(c_182,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_15])).

cnf(c_183,plain,
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
    inference(renaming,[status(thm)],[c_182])).

cnf(c_819,plain,
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
    inference(resolution_lifted,[status(thm)],[c_183,c_27])).

cnf(c_820,plain,
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
    inference(unflattening,[status(thm)],[c_819])).

cnf(c_824,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_820,c_28])).

cnf(c_825,plain,
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
    inference(renaming,[status(thm)],[c_824])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_860,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_825,c_5])).

cnf(c_1480,plain,
    ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,sK2,X0_53),X0_54)
    | ~ r1_tmap_1(X2_53,X1_53,sK2,X0_54)
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | u1_struct_0(X2_53) != u1_struct_0(sK1)
    | u1_struct_0(X1_53) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_860])).

cnf(c_2708,plain,
    ( r1_tmap_1(X0_53,sK0,k2_tmap_1(X1_53,sK0,sK2,X0_53),X0_54)
    | ~ r1_tmap_1(X1_53,sK0,sK2,X0_54)
    | ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(sK0))))
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1480])).

cnf(c_3222,plain,
    ( ~ r1_tmap_1(X0_53,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(X0_53,sK0,sK2,sK3),sK5)
    | ~ m1_pre_topc(sK3,X0_53)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK0))))
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0_53)
    | v2_struct_0(sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(X0_53) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2708])).

cnf(c_3223,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | r1_tmap_1(X0_53,sK0,sK2,sK5) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(X0_53,sK0,sK2,sK3),sK5) = iProver_top
    | m1_pre_topc(sK3,X0_53) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK0)))) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3222])).

cnf(c_3225,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3223])).

cnf(c_3289,plain,
    ( m1_pre_topc(sK3,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3114,c_35,c_36,c_37,c_38,c_39,c_40,c_43,c_44,c_46,c_48,c_2161,c_2319,c_2706,c_3225])).

cnf(c_3294,plain,
    ( l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2082,c_3289])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3294,c_2518,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n006.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 18:13:52 EST 2020
% 0.17/0.32  % CPUTime    : 
% 0.17/0.32  % Running in FOF mode
% 1.85/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/0.96  
% 1.85/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.85/0.96  
% 1.85/0.96  ------  iProver source info
% 1.85/0.96  
% 1.85/0.96  git: date: 2020-06-30 10:37:57 +0100
% 1.85/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.85/0.96  git: non_committed_changes: false
% 1.85/0.96  git: last_make_outside_of_git: false
% 1.85/0.96  
% 1.85/0.96  ------ 
% 1.85/0.96  
% 1.85/0.96  ------ Input Options
% 1.85/0.96  
% 1.85/0.96  --out_options                           all
% 1.85/0.96  --tptp_safe_out                         true
% 1.85/0.96  --problem_path                          ""
% 1.85/0.96  --include_path                          ""
% 1.85/0.96  --clausifier                            res/vclausify_rel
% 1.85/0.96  --clausifier_options                    --mode clausify
% 1.85/0.96  --stdin                                 false
% 1.85/0.96  --stats_out                             all
% 1.85/0.96  
% 1.85/0.96  ------ General Options
% 1.85/0.96  
% 1.85/0.96  --fof                                   false
% 1.85/0.96  --time_out_real                         305.
% 1.85/0.96  --time_out_virtual                      -1.
% 1.85/0.96  --symbol_type_check                     false
% 1.85/0.96  --clausify_out                          false
% 1.85/0.96  --sig_cnt_out                           false
% 1.85/0.96  --trig_cnt_out                          false
% 1.85/0.96  --trig_cnt_out_tolerance                1.
% 1.85/0.96  --trig_cnt_out_sk_spl                   false
% 1.85/0.96  --abstr_cl_out                          false
% 1.85/0.96  
% 1.85/0.96  ------ Global Options
% 1.85/0.96  
% 1.85/0.96  --schedule                              default
% 1.85/0.96  --add_important_lit                     false
% 1.85/0.96  --prop_solver_per_cl                    1000
% 1.85/0.96  --min_unsat_core                        false
% 1.85/0.96  --soft_assumptions                      false
% 1.85/0.96  --soft_lemma_size                       3
% 1.85/0.96  --prop_impl_unit_size                   0
% 1.85/0.96  --prop_impl_unit                        []
% 1.85/0.96  --share_sel_clauses                     true
% 1.85/0.96  --reset_solvers                         false
% 1.85/0.96  --bc_imp_inh                            [conj_cone]
% 1.85/0.96  --conj_cone_tolerance                   3.
% 1.85/0.96  --extra_neg_conj                        none
% 1.85/0.96  --large_theory_mode                     true
% 1.85/0.96  --prolific_symb_bound                   200
% 1.85/0.96  --lt_threshold                          2000
% 1.85/0.96  --clause_weak_htbl                      true
% 1.85/0.96  --gc_record_bc_elim                     false
% 1.85/0.96  
% 1.85/0.96  ------ Preprocessing Options
% 1.85/0.96  
% 1.85/0.96  --preprocessing_flag                    true
% 1.85/0.96  --time_out_prep_mult                    0.1
% 1.85/0.96  --splitting_mode                        input
% 1.85/0.96  --splitting_grd                         true
% 1.85/0.96  --splitting_cvd                         false
% 1.85/0.96  --splitting_cvd_svl                     false
% 1.85/0.96  --splitting_nvd                         32
% 1.85/0.96  --sub_typing                            true
% 1.85/0.96  --prep_gs_sim                           true
% 1.85/0.96  --prep_unflatten                        true
% 1.85/0.96  --prep_res_sim                          true
% 1.85/0.96  --prep_upred                            true
% 1.85/0.96  --prep_sem_filter                       exhaustive
% 1.85/0.96  --prep_sem_filter_out                   false
% 1.85/0.96  --pred_elim                             true
% 1.85/0.96  --res_sim_input                         true
% 1.85/0.96  --eq_ax_congr_red                       true
% 1.85/0.96  --pure_diseq_elim                       true
% 1.85/0.96  --brand_transform                       false
% 1.85/0.96  --non_eq_to_eq                          false
% 1.85/0.96  --prep_def_merge                        true
% 1.85/0.96  --prep_def_merge_prop_impl              false
% 1.85/0.96  --prep_def_merge_mbd                    true
% 1.85/0.96  --prep_def_merge_tr_red                 false
% 1.85/0.96  --prep_def_merge_tr_cl                  false
% 1.85/0.96  --smt_preprocessing                     true
% 1.85/0.96  --smt_ac_axioms                         fast
% 1.85/0.96  --preprocessed_out                      false
% 1.85/0.96  --preprocessed_stats                    false
% 1.85/0.96  
% 1.85/0.96  ------ Abstraction refinement Options
% 1.85/0.96  
% 1.85/0.96  --abstr_ref                             []
% 1.85/0.96  --abstr_ref_prep                        false
% 1.85/0.96  --abstr_ref_until_sat                   false
% 1.85/0.96  --abstr_ref_sig_restrict                funpre
% 1.85/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.85/0.96  --abstr_ref_under                       []
% 1.85/0.96  
% 1.85/0.96  ------ SAT Options
% 1.85/0.96  
% 1.85/0.96  --sat_mode                              false
% 1.85/0.96  --sat_fm_restart_options                ""
% 1.85/0.96  --sat_gr_def                            false
% 1.85/0.96  --sat_epr_types                         true
% 1.85/0.96  --sat_non_cyclic_types                  false
% 1.85/0.96  --sat_finite_models                     false
% 1.85/0.96  --sat_fm_lemmas                         false
% 1.85/0.96  --sat_fm_prep                           false
% 1.85/0.96  --sat_fm_uc_incr                        true
% 1.85/0.96  --sat_out_model                         small
% 1.85/0.96  --sat_out_clauses                       false
% 1.85/0.96  
% 1.85/0.96  ------ QBF Options
% 1.85/0.96  
% 1.85/0.96  --qbf_mode                              false
% 1.85/0.96  --qbf_elim_univ                         false
% 1.85/0.96  --qbf_dom_inst                          none
% 1.85/0.96  --qbf_dom_pre_inst                      false
% 1.85/0.96  --qbf_sk_in                             false
% 1.85/0.96  --qbf_pred_elim                         true
% 1.85/0.96  --qbf_split                             512
% 1.85/0.96  
% 1.85/0.96  ------ BMC1 Options
% 1.85/0.96  
% 1.85/0.96  --bmc1_incremental                      false
% 1.85/0.96  --bmc1_axioms                           reachable_all
% 1.85/0.96  --bmc1_min_bound                        0
% 1.85/0.96  --bmc1_max_bound                        -1
% 1.85/0.96  --bmc1_max_bound_default                -1
% 1.85/0.96  --bmc1_symbol_reachability              true
% 1.85/0.96  --bmc1_property_lemmas                  false
% 1.85/0.96  --bmc1_k_induction                      false
% 1.85/0.96  --bmc1_non_equiv_states                 false
% 1.85/0.96  --bmc1_deadlock                         false
% 1.85/0.96  --bmc1_ucm                              false
% 1.85/0.96  --bmc1_add_unsat_core                   none
% 1.85/0.96  --bmc1_unsat_core_children              false
% 1.85/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.85/0.96  --bmc1_out_stat                         full
% 1.85/0.96  --bmc1_ground_init                      false
% 1.85/0.96  --bmc1_pre_inst_next_state              false
% 1.85/0.96  --bmc1_pre_inst_state                   false
% 1.85/0.96  --bmc1_pre_inst_reach_state             false
% 1.85/0.96  --bmc1_out_unsat_core                   false
% 1.85/0.96  --bmc1_aig_witness_out                  false
% 1.85/0.96  --bmc1_verbose                          false
% 1.85/0.96  --bmc1_dump_clauses_tptp                false
% 1.85/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.85/0.96  --bmc1_dump_file                        -
% 1.85/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.85/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.85/0.96  --bmc1_ucm_extend_mode                  1
% 1.85/0.96  --bmc1_ucm_init_mode                    2
% 1.85/0.96  --bmc1_ucm_cone_mode                    none
% 1.85/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.85/0.96  --bmc1_ucm_relax_model                  4
% 1.85/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.85/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.85/0.96  --bmc1_ucm_layered_model                none
% 1.85/0.96  --bmc1_ucm_max_lemma_size               10
% 1.85/0.96  
% 1.85/0.96  ------ AIG Options
% 1.85/0.96  
% 1.85/0.96  --aig_mode                              false
% 1.85/0.96  
% 1.85/0.96  ------ Instantiation Options
% 1.85/0.96  
% 1.85/0.96  --instantiation_flag                    true
% 1.85/0.96  --inst_sos_flag                         false
% 1.85/0.96  --inst_sos_phase                        true
% 1.85/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.85/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.85/0.96  --inst_lit_sel_side                     num_symb
% 1.85/0.96  --inst_solver_per_active                1400
% 1.85/0.96  --inst_solver_calls_frac                1.
% 1.85/0.96  --inst_passive_queue_type               priority_queues
% 1.85/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.85/0.96  --inst_passive_queues_freq              [25;2]
% 1.85/0.96  --inst_dismatching                      true
% 1.85/0.96  --inst_eager_unprocessed_to_passive     true
% 1.85/0.96  --inst_prop_sim_given                   true
% 1.85/0.96  --inst_prop_sim_new                     false
% 1.85/0.96  --inst_subs_new                         false
% 1.85/0.96  --inst_eq_res_simp                      false
% 1.85/0.96  --inst_subs_given                       false
% 1.85/0.96  --inst_orphan_elimination               true
% 1.85/0.96  --inst_learning_loop_flag               true
% 1.85/0.96  --inst_learning_start                   3000
% 1.85/0.96  --inst_learning_factor                  2
% 1.85/0.96  --inst_start_prop_sim_after_learn       3
% 1.85/0.96  --inst_sel_renew                        solver
% 1.85/0.96  --inst_lit_activity_flag                true
% 1.85/0.96  --inst_restr_to_given                   false
% 1.85/0.96  --inst_activity_threshold               500
% 1.85/0.96  --inst_out_proof                        true
% 1.85/0.96  
% 1.85/0.96  ------ Resolution Options
% 1.85/0.96  
% 1.85/0.96  --resolution_flag                       true
% 1.85/0.96  --res_lit_sel                           adaptive
% 1.85/0.96  --res_lit_sel_side                      none
% 1.85/0.96  --res_ordering                          kbo
% 1.85/0.96  --res_to_prop_solver                    active
% 1.85/0.96  --res_prop_simpl_new                    false
% 1.85/0.96  --res_prop_simpl_given                  true
% 1.85/0.96  --res_passive_queue_type                priority_queues
% 1.85/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.85/0.96  --res_passive_queues_freq               [15;5]
% 1.85/0.96  --res_forward_subs                      full
% 1.85/0.96  --res_backward_subs                     full
% 1.85/0.96  --res_forward_subs_resolution           true
% 1.85/0.96  --res_backward_subs_resolution          true
% 1.85/0.96  --res_orphan_elimination                true
% 1.85/0.96  --res_time_limit                        2.
% 1.85/0.96  --res_out_proof                         true
% 1.85/0.96  
% 1.85/0.96  ------ Superposition Options
% 1.85/0.96  
% 1.85/0.96  --superposition_flag                    true
% 1.85/0.96  --sup_passive_queue_type                priority_queues
% 1.85/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.85/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.85/0.96  --demod_completeness_check              fast
% 1.85/0.96  --demod_use_ground                      true
% 1.85/0.96  --sup_to_prop_solver                    passive
% 1.85/0.96  --sup_prop_simpl_new                    true
% 1.85/0.96  --sup_prop_simpl_given                  true
% 1.85/0.96  --sup_fun_splitting                     false
% 1.85/0.96  --sup_smt_interval                      50000
% 1.85/0.96  
% 1.85/0.96  ------ Superposition Simplification Setup
% 1.85/0.96  
% 1.85/0.96  --sup_indices_passive                   []
% 1.85/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.85/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/0.96  --sup_full_bw                           [BwDemod]
% 1.85/0.96  --sup_immed_triv                        [TrivRules]
% 1.85/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.85/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/0.96  --sup_immed_bw_main                     []
% 1.85/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.85/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/0.96  
% 1.85/0.96  ------ Combination Options
% 1.85/0.96  
% 1.85/0.96  --comb_res_mult                         3
% 1.85/0.96  --comb_sup_mult                         2
% 1.85/0.96  --comb_inst_mult                        10
% 1.85/0.96  
% 1.85/0.96  ------ Debug Options
% 1.85/0.96  
% 1.85/0.96  --dbg_backtrace                         false
% 1.85/0.96  --dbg_dump_prop_clauses                 false
% 1.85/0.96  --dbg_dump_prop_clauses_file            -
% 1.85/0.96  --dbg_out_stat                          false
% 1.85/0.96  ------ Parsing...
% 1.85/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.85/0.96  
% 1.85/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.85/0.96  
% 1.85/0.96  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.85/0.96  
% 1.85/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.85/0.96  ------ Proving...
% 1.85/0.96  ------ Problem Properties 
% 1.85/0.96  
% 1.85/0.96  
% 1.85/0.96  clauses                                 25
% 1.85/0.96  conjectures                             14
% 1.85/0.96  EPR                                     11
% 1.85/0.96  Horn                                    19
% 1.85/0.96  unary                                   12
% 1.85/0.96  binary                                  3
% 1.85/0.96  lits                                    79
% 1.85/0.96  lits eq                                 4
% 1.85/0.96  fd_pure                                 0
% 1.85/0.96  fd_pseudo                               0
% 1.85/0.96  fd_cond                                 0
% 1.85/0.96  fd_pseudo_cond                          0
% 1.85/0.96  AC symbols                              0
% 1.85/0.96  
% 1.85/0.96  ------ Schedule dynamic 5 is on 
% 1.85/0.96  
% 1.85/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.85/0.96  
% 1.85/0.96  
% 1.85/0.96  ------ 
% 1.85/0.96  Current options:
% 1.85/0.96  ------ 
% 1.85/0.96  
% 1.85/0.96  ------ Input Options
% 1.85/0.96  
% 1.85/0.96  --out_options                           all
% 1.85/0.96  --tptp_safe_out                         true
% 1.85/0.96  --problem_path                          ""
% 1.85/0.96  --include_path                          ""
% 1.85/0.96  --clausifier                            res/vclausify_rel
% 1.85/0.96  --clausifier_options                    --mode clausify
% 1.85/0.96  --stdin                                 false
% 1.85/0.96  --stats_out                             all
% 1.85/0.96  
% 1.85/0.96  ------ General Options
% 1.85/0.96  
% 1.85/0.96  --fof                                   false
% 1.85/0.96  --time_out_real                         305.
% 1.85/0.96  --time_out_virtual                      -1.
% 1.85/0.96  --symbol_type_check                     false
% 1.85/0.96  --clausify_out                          false
% 1.85/0.96  --sig_cnt_out                           false
% 1.85/0.96  --trig_cnt_out                          false
% 1.85/0.96  --trig_cnt_out_tolerance                1.
% 1.85/0.96  --trig_cnt_out_sk_spl                   false
% 1.85/0.96  --abstr_cl_out                          false
% 1.85/0.96  
% 1.85/0.96  ------ Global Options
% 1.85/0.96  
% 1.85/0.96  --schedule                              default
% 1.85/0.96  --add_important_lit                     false
% 1.85/0.96  --prop_solver_per_cl                    1000
% 1.85/0.96  --min_unsat_core                        false
% 1.85/0.96  --soft_assumptions                      false
% 1.85/0.96  --soft_lemma_size                       3
% 1.85/0.96  --prop_impl_unit_size                   0
% 1.85/0.96  --prop_impl_unit                        []
% 1.85/0.96  --share_sel_clauses                     true
% 1.85/0.96  --reset_solvers                         false
% 1.85/0.96  --bc_imp_inh                            [conj_cone]
% 1.85/0.96  --conj_cone_tolerance                   3.
% 1.85/0.96  --extra_neg_conj                        none
% 1.85/0.96  --large_theory_mode                     true
% 1.85/0.96  --prolific_symb_bound                   200
% 1.85/0.96  --lt_threshold                          2000
% 1.85/0.96  --clause_weak_htbl                      true
% 1.85/0.96  --gc_record_bc_elim                     false
% 1.85/0.96  
% 1.85/0.96  ------ Preprocessing Options
% 1.85/0.96  
% 1.85/0.96  --preprocessing_flag                    true
% 1.85/0.96  --time_out_prep_mult                    0.1
% 1.85/0.96  --splitting_mode                        input
% 1.85/0.96  --splitting_grd                         true
% 1.85/0.96  --splitting_cvd                         false
% 1.85/0.96  --splitting_cvd_svl                     false
% 1.85/0.96  --splitting_nvd                         32
% 1.85/0.96  --sub_typing                            true
% 1.85/0.96  --prep_gs_sim                           true
% 1.85/0.96  --prep_unflatten                        true
% 1.85/0.96  --prep_res_sim                          true
% 1.85/0.96  --prep_upred                            true
% 1.85/0.96  --prep_sem_filter                       exhaustive
% 1.85/0.96  --prep_sem_filter_out                   false
% 1.85/0.96  --pred_elim                             true
% 1.85/0.96  --res_sim_input                         true
% 1.85/0.96  --eq_ax_congr_red                       true
% 1.85/0.96  --pure_diseq_elim                       true
% 1.85/0.96  --brand_transform                       false
% 1.85/0.96  --non_eq_to_eq                          false
% 1.85/0.96  --prep_def_merge                        true
% 1.85/0.96  --prep_def_merge_prop_impl              false
% 1.85/0.96  --prep_def_merge_mbd                    true
% 1.85/0.96  --prep_def_merge_tr_red                 false
% 1.85/0.96  --prep_def_merge_tr_cl                  false
% 1.85/0.96  --smt_preprocessing                     true
% 1.85/0.96  --smt_ac_axioms                         fast
% 1.85/0.96  --preprocessed_out                      false
% 1.85/0.96  --preprocessed_stats                    false
% 1.85/0.96  
% 1.85/0.96  ------ Abstraction refinement Options
% 1.85/0.96  
% 1.85/0.96  --abstr_ref                             []
% 1.85/0.96  --abstr_ref_prep                        false
% 1.85/0.96  --abstr_ref_until_sat                   false
% 1.85/0.96  --abstr_ref_sig_restrict                funpre
% 1.85/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.85/0.96  --abstr_ref_under                       []
% 1.85/0.96  
% 1.85/0.96  ------ SAT Options
% 1.85/0.96  
% 1.85/0.96  --sat_mode                              false
% 1.85/0.96  --sat_fm_restart_options                ""
% 1.85/0.96  --sat_gr_def                            false
% 1.85/0.96  --sat_epr_types                         true
% 1.85/0.96  --sat_non_cyclic_types                  false
% 1.85/0.96  --sat_finite_models                     false
% 1.85/0.96  --sat_fm_lemmas                         false
% 1.85/0.96  --sat_fm_prep                           false
% 1.85/0.96  --sat_fm_uc_incr                        true
% 1.85/0.96  --sat_out_model                         small
% 1.85/0.96  --sat_out_clauses                       false
% 1.85/0.96  
% 1.85/0.96  ------ QBF Options
% 1.85/0.96  
% 1.85/0.96  --qbf_mode                              false
% 1.85/0.96  --qbf_elim_univ                         false
% 1.85/0.96  --qbf_dom_inst                          none
% 1.85/0.96  --qbf_dom_pre_inst                      false
% 1.85/0.96  --qbf_sk_in                             false
% 1.85/0.96  --qbf_pred_elim                         true
% 1.85/0.96  --qbf_split                             512
% 1.85/0.96  
% 1.85/0.96  ------ BMC1 Options
% 1.85/0.96  
% 1.85/0.96  --bmc1_incremental                      false
% 1.85/0.96  --bmc1_axioms                           reachable_all
% 1.85/0.96  --bmc1_min_bound                        0
% 1.85/0.96  --bmc1_max_bound                        -1
% 1.85/0.96  --bmc1_max_bound_default                -1
% 1.85/0.96  --bmc1_symbol_reachability              true
% 1.85/0.96  --bmc1_property_lemmas                  false
% 1.85/0.96  --bmc1_k_induction                      false
% 1.85/0.96  --bmc1_non_equiv_states                 false
% 1.85/0.96  --bmc1_deadlock                         false
% 1.85/0.96  --bmc1_ucm                              false
% 1.85/0.96  --bmc1_add_unsat_core                   none
% 1.85/0.96  --bmc1_unsat_core_children              false
% 1.85/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.85/0.96  --bmc1_out_stat                         full
% 1.85/0.96  --bmc1_ground_init                      false
% 1.85/0.96  --bmc1_pre_inst_next_state              false
% 1.85/0.96  --bmc1_pre_inst_state                   false
% 1.85/0.96  --bmc1_pre_inst_reach_state             false
% 1.85/0.96  --bmc1_out_unsat_core                   false
% 1.85/0.96  --bmc1_aig_witness_out                  false
% 1.85/0.96  --bmc1_verbose                          false
% 1.85/0.96  --bmc1_dump_clauses_tptp                false
% 1.85/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.85/0.96  --bmc1_dump_file                        -
% 1.85/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.85/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.85/0.96  --bmc1_ucm_extend_mode                  1
% 1.85/0.96  --bmc1_ucm_init_mode                    2
% 1.85/0.96  --bmc1_ucm_cone_mode                    none
% 1.85/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.85/0.96  --bmc1_ucm_relax_model                  4
% 1.85/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.85/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.85/0.96  --bmc1_ucm_layered_model                none
% 1.85/0.96  --bmc1_ucm_max_lemma_size               10
% 1.85/0.96  
% 1.85/0.96  ------ AIG Options
% 1.85/0.96  
% 1.85/0.96  --aig_mode                              false
% 1.85/0.96  
% 1.85/0.96  ------ Instantiation Options
% 1.85/0.96  
% 1.85/0.96  --instantiation_flag                    true
% 1.85/0.96  --inst_sos_flag                         false
% 1.85/0.96  --inst_sos_phase                        true
% 1.85/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.85/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.85/0.96  --inst_lit_sel_side                     none
% 1.85/0.96  --inst_solver_per_active                1400
% 1.85/0.96  --inst_solver_calls_frac                1.
% 1.85/0.96  --inst_passive_queue_type               priority_queues
% 1.85/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.85/0.96  --inst_passive_queues_freq              [25;2]
% 1.85/0.96  --inst_dismatching                      true
% 1.85/0.96  --inst_eager_unprocessed_to_passive     true
% 1.85/0.96  --inst_prop_sim_given                   true
% 1.85/0.96  --inst_prop_sim_new                     false
% 1.85/0.96  --inst_subs_new                         false
% 1.85/0.96  --inst_eq_res_simp                      false
% 1.85/0.96  --inst_subs_given                       false
% 1.85/0.96  --inst_orphan_elimination               true
% 1.85/0.96  --inst_learning_loop_flag               true
% 1.85/0.96  --inst_learning_start                   3000
% 1.85/0.96  --inst_learning_factor                  2
% 1.85/0.96  --inst_start_prop_sim_after_learn       3
% 1.85/0.96  --inst_sel_renew                        solver
% 1.85/0.96  --inst_lit_activity_flag                true
% 1.85/0.96  --inst_restr_to_given                   false
% 1.85/0.96  --inst_activity_threshold               500
% 1.85/0.96  --inst_out_proof                        true
% 1.85/0.96  
% 1.85/0.96  ------ Resolution Options
% 1.85/0.96  
% 1.85/0.96  --resolution_flag                       false
% 1.85/0.96  --res_lit_sel                           adaptive
% 1.85/0.96  --res_lit_sel_side                      none
% 1.85/0.96  --res_ordering                          kbo
% 1.85/0.96  --res_to_prop_solver                    active
% 1.85/0.96  --res_prop_simpl_new                    false
% 1.85/0.96  --res_prop_simpl_given                  true
% 1.85/0.96  --res_passive_queue_type                priority_queues
% 1.85/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.85/0.96  --res_passive_queues_freq               [15;5]
% 1.85/0.96  --res_forward_subs                      full
% 1.85/0.96  --res_backward_subs                     full
% 1.85/0.96  --res_forward_subs_resolution           true
% 1.85/0.96  --res_backward_subs_resolution          true
% 1.85/0.96  --res_orphan_elimination                true
% 1.85/0.96  --res_time_limit                        2.
% 1.85/0.96  --res_out_proof                         true
% 1.85/0.96  
% 1.85/0.96  ------ Superposition Options
% 1.85/0.96  
% 1.85/0.96  --superposition_flag                    true
% 1.85/0.96  --sup_passive_queue_type                priority_queues
% 1.85/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.85/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.85/0.96  --demod_completeness_check              fast
% 1.85/0.96  --demod_use_ground                      true
% 1.85/0.96  --sup_to_prop_solver                    passive
% 1.85/0.96  --sup_prop_simpl_new                    true
% 1.85/0.96  --sup_prop_simpl_given                  true
% 1.85/0.96  --sup_fun_splitting                     false
% 1.85/0.96  --sup_smt_interval                      50000
% 1.85/0.96  
% 1.85/0.96  ------ Superposition Simplification Setup
% 1.85/0.96  
% 1.85/0.96  --sup_indices_passive                   []
% 1.85/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.85/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/0.96  --sup_full_bw                           [BwDemod]
% 1.85/0.96  --sup_immed_triv                        [TrivRules]
% 1.85/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.85/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/0.96  --sup_immed_bw_main                     []
% 1.85/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.85/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/0.96  
% 1.85/0.96  ------ Combination Options
% 1.85/0.96  
% 1.85/0.96  --comb_res_mult                         3
% 1.85/0.96  --comb_sup_mult                         2
% 1.85/0.96  --comb_inst_mult                        10
% 1.85/0.96  
% 1.85/0.96  ------ Debug Options
% 1.85/0.96  
% 1.85/0.96  --dbg_backtrace                         false
% 1.85/0.96  --dbg_dump_prop_clauses                 false
% 1.85/0.96  --dbg_dump_prop_clauses_file            -
% 1.85/0.96  --dbg_out_stat                          false
% 1.85/0.96  
% 1.85/0.96  
% 1.85/0.96  
% 1.85/0.96  
% 1.85/0.96  ------ Proving...
% 1.85/0.96  
% 1.85/0.96  
% 1.85/0.96  % SZS status Theorem for theBenchmark.p
% 1.85/0.96  
% 1.85/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 1.85/0.96  
% 1.85/0.96  fof(f11,axiom,(
% 1.85/0.96    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.85/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/0.96  
% 1.85/0.96  fof(f34,plain,(
% 1.85/0.96    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.85/0.96    inference(ennf_transformation,[],[f11])).
% 1.85/0.96  
% 1.85/0.96  fof(f68,plain,(
% 1.85/0.96    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.85/0.96    inference(cnf_transformation,[],[f34])).
% 1.85/0.96  
% 1.85/0.96  fof(f15,conjecture,(
% 1.85/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.85/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/0.96  
% 1.85/0.96  fof(f16,negated_conjecture,(
% 1.85/0.96    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.85/0.96    inference(negated_conjecture,[],[f15])).
% 1.85/0.96  
% 1.85/0.96  fof(f41,plain,(
% 1.85/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.85/0.96    inference(ennf_transformation,[],[f16])).
% 1.85/0.96  
% 1.85/0.96  fof(f42,plain,(
% 1.85/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.85/0.96    inference(flattening,[],[f41])).
% 1.85/0.96  
% 1.85/0.96  fof(f47,plain,(
% 1.85/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.85/0.96    inference(nnf_transformation,[],[f42])).
% 1.85/0.96  
% 1.85/0.96  fof(f48,plain,(
% 1.85/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.85/0.96    inference(flattening,[],[f47])).
% 1.85/0.96  
% 1.85/0.96  fof(f54,plain,(
% 1.85/0.96    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK5) | r1_tmap_1(X1,X0,X2,X4)) & sK5 = X4 & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 1.85/0.96    introduced(choice_axiom,[])).
% 1.85/0.96  
% 1.85/0.96  fof(f53,plain,(
% 1.85/0.96    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK4)) & sK4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 1.85/0.96    introduced(choice_axiom,[])).
% 1.85/0.96  
% 1.85/0.96  fof(f52,plain,(
% 1.85/0.96    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK3,X1) & v1_tsep_1(sK3,X1) & ~v2_struct_0(sK3))) )),
% 1.85/0.96    introduced(choice_axiom,[])).
% 1.85/0.96  
% 1.85/0.96  fof(f51,plain,(
% 1.85/0.96    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X5) | ~r1_tmap_1(X1,X0,sK2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X5) | r1_tmap_1(X1,X0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK2))) )),
% 1.85/0.96    introduced(choice_axiom,[])).
% 1.85/0.96  
% 1.85/0.96  fof(f50,plain,(
% 1.85/0.96    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X5) | ~r1_tmap_1(sK1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X5) | r1_tmap_1(sK1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.85/0.96    introduced(choice_axiom,[])).
% 1.85/0.96  
% 1.85/0.96  fof(f49,plain,(
% 1.85/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | ~r1_tmap_1(X1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | r1_tmap_1(X1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.85/0.96    introduced(choice_axiom,[])).
% 1.85/0.96  
% 1.85/0.96  fof(f55,plain,(
% 1.85/0.96    ((((((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.85/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f48,f54,f53,f52,f51,f50,f49])).
% 1.85/0.96  
% 1.85/0.96  fof(f85,plain,(
% 1.85/0.96    m1_pre_topc(sK3,sK1)),
% 1.85/0.96    inference(cnf_transformation,[],[f55])).
% 1.85/0.96  
% 1.85/0.96  fof(f12,axiom,(
% 1.85/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 1.85/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/0.96  
% 1.85/0.96  fof(f35,plain,(
% 1.85/0.96    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.85/0.96    inference(ennf_transformation,[],[f12])).
% 1.85/0.96  
% 1.85/0.96  fof(f36,plain,(
% 1.85/0.96    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.85/0.96    inference(flattening,[],[f35])).
% 1.85/0.96  
% 1.85/0.96  fof(f45,plain,(
% 1.85/0.96    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.85/0.96    inference(nnf_transformation,[],[f36])).
% 1.85/0.96  
% 1.85/0.96  fof(f70,plain,(
% 1.85/0.96    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.85/0.96    inference(cnf_transformation,[],[f45])).
% 1.85/0.96  
% 1.85/0.96  fof(f78,plain,(
% 1.85/0.96    v2_pre_topc(sK1)),
% 1.85/0.96    inference(cnf_transformation,[],[f55])).
% 1.85/0.96  
% 1.85/0.96  fof(f79,plain,(
% 1.85/0.96    l1_pre_topc(sK1)),
% 1.85/0.96    inference(cnf_transformation,[],[f55])).
% 1.85/0.96  
% 1.85/0.96  fof(f89,plain,(
% 1.85/0.96    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 1.85/0.96    inference(cnf_transformation,[],[f55])).
% 1.85/0.96  
% 1.85/0.96  fof(f88,plain,(
% 1.85/0.96    sK4 = sK5),
% 1.85/0.96    inference(cnf_transformation,[],[f55])).
% 1.85/0.96  
% 1.85/0.96  fof(f81,plain,(
% 1.85/0.96    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.85/0.96    inference(cnf_transformation,[],[f55])).
% 1.85/0.96  
% 1.85/0.96  fof(f14,axiom,(
% 1.85/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.85/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/0.96  
% 1.85/0.96  fof(f39,plain,(
% 1.85/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.85/0.96    inference(ennf_transformation,[],[f14])).
% 1.85/0.96  
% 1.85/0.96  fof(f40,plain,(
% 1.85/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.85/0.96    inference(flattening,[],[f39])).
% 1.85/0.96  
% 1.85/0.96  fof(f46,plain,(
% 1.85/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.85/0.96    inference(nnf_transformation,[],[f40])).
% 1.85/0.96  
% 1.85/0.96  fof(f73,plain,(
% 1.85/0.96    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.85/0.96    inference(cnf_transformation,[],[f46])).
% 1.85/0.96  
% 1.85/0.96  fof(f95,plain,(
% 1.85/0.96    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.85/0.96    inference(equality_resolution,[],[f73])).
% 1.85/0.96  
% 1.85/0.96  fof(f1,axiom,(
% 1.85/0.96    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.85/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/0.96  
% 1.85/0.96  fof(f17,plain,(
% 1.85/0.96    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.85/0.96    inference(ennf_transformation,[],[f1])).
% 1.85/0.96  
% 1.85/0.96  fof(f18,plain,(
% 1.85/0.96    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.85/0.96    inference(flattening,[],[f17])).
% 1.85/0.96  
% 1.85/0.96  fof(f56,plain,(
% 1.85/0.96    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.85/0.96    inference(cnf_transformation,[],[f18])).
% 1.85/0.96  
% 1.85/0.96  fof(f8,axiom,(
% 1.85/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 1.85/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/0.96  
% 1.85/0.96  fof(f29,plain,(
% 1.85/0.96    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.85/0.96    inference(ennf_transformation,[],[f8])).
% 1.85/0.96  
% 1.85/0.96  fof(f30,plain,(
% 1.85/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.85/0.96    inference(flattening,[],[f29])).
% 1.85/0.96  
% 1.85/0.96  fof(f63,plain,(
% 1.85/0.96    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.85/0.96    inference(cnf_transformation,[],[f30])).
% 1.85/0.96  
% 1.85/0.96  fof(f9,axiom,(
% 1.85/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.85/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/0.96  
% 1.85/0.96  fof(f31,plain,(
% 1.85/0.96    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.85/0.96    inference(ennf_transformation,[],[f9])).
% 1.85/0.96  
% 1.85/0.96  fof(f32,plain,(
% 1.85/0.96    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.85/0.96    inference(flattening,[],[f31])).
% 1.85/0.96  
% 1.85/0.96  fof(f43,plain,(
% 1.85/0.96    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.85/0.96    inference(nnf_transformation,[],[f32])).
% 1.85/0.96  
% 1.85/0.96  fof(f44,plain,(
% 1.85/0.96    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.85/0.96    inference(flattening,[],[f43])).
% 1.85/0.96  
% 1.85/0.96  fof(f64,plain,(
% 1.85/0.96    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.85/0.96    inference(cnf_transformation,[],[f44])).
% 1.85/0.96  
% 1.85/0.96  fof(f93,plain,(
% 1.85/0.96    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.85/0.96    inference(equality_resolution,[],[f64])).
% 1.85/0.96  
% 1.85/0.96  fof(f10,axiom,(
% 1.85/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.85/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/0.96  
% 1.85/0.96  fof(f33,plain,(
% 1.85/0.96    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.85/0.96    inference(ennf_transformation,[],[f10])).
% 1.85/0.96  
% 1.85/0.96  fof(f67,plain,(
% 1.85/0.96    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.85/0.96    inference(cnf_transformation,[],[f33])).
% 1.85/0.96  
% 1.85/0.96  fof(f84,plain,(
% 1.85/0.96    v1_tsep_1(sK3,sK1)),
% 1.85/0.96    inference(cnf_transformation,[],[f55])).
% 1.85/0.96  
% 1.85/0.96  fof(f77,plain,(
% 1.85/0.96    ~v2_struct_0(sK1)),
% 1.85/0.96    inference(cnf_transformation,[],[f55])).
% 1.85/0.96  
% 1.85/0.96  fof(f2,axiom,(
% 1.85/0.96    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.85/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/0.96  
% 1.85/0.96  fof(f19,plain,(
% 1.85/0.96    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.85/0.96    inference(ennf_transformation,[],[f2])).
% 1.85/0.96  
% 1.85/0.96  fof(f20,plain,(
% 1.85/0.96    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.85/0.96    inference(flattening,[],[f19])).
% 1.85/0.96  
% 1.85/0.96  fof(f57,plain,(
% 1.85/0.96    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.85/0.96    inference(cnf_transformation,[],[f20])).
% 1.85/0.96  
% 1.85/0.96  fof(f80,plain,(
% 1.85/0.96    v1_funct_1(sK2)),
% 1.85/0.96    inference(cnf_transformation,[],[f55])).
% 1.85/0.96  
% 1.85/0.96  fof(f83,plain,(
% 1.85/0.96    ~v2_struct_0(sK3)),
% 1.85/0.96    inference(cnf_transformation,[],[f55])).
% 1.85/0.96  
% 1.85/0.96  fof(f3,axiom,(
% 1.85/0.96    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.85/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/0.96  
% 1.85/0.96  fof(f21,plain,(
% 1.85/0.96    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.85/0.96    inference(ennf_transformation,[],[f3])).
% 1.85/0.96  
% 1.85/0.96  fof(f58,plain,(
% 1.85/0.96    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.85/0.96    inference(cnf_transformation,[],[f21])).
% 1.85/0.96  
% 1.85/0.96  fof(f5,axiom,(
% 1.85/0.96    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.85/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/0.96  
% 1.85/0.96  fof(f23,plain,(
% 1.85/0.96    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.85/0.96    inference(ennf_transformation,[],[f5])).
% 1.85/0.96  
% 1.85/0.96  fof(f24,plain,(
% 1.85/0.96    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.85/0.96    inference(flattening,[],[f23])).
% 1.85/0.96  
% 1.85/0.96  fof(f60,plain,(
% 1.85/0.96    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.85/0.96    inference(cnf_transformation,[],[f24])).
% 1.85/0.96  
% 1.85/0.96  fof(f4,axiom,(
% 1.85/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.85/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/0.96  
% 1.85/0.96  fof(f22,plain,(
% 1.85/0.96    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.85/0.96    inference(ennf_transformation,[],[f4])).
% 1.85/0.96  
% 1.85/0.96  fof(f59,plain,(
% 1.85/0.96    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.85/0.96    inference(cnf_transformation,[],[f22])).
% 1.85/0.96  
% 1.85/0.96  fof(f74,plain,(
% 1.85/0.96    ~v2_struct_0(sK0)),
% 1.85/0.96    inference(cnf_transformation,[],[f55])).
% 1.85/0.96  
% 1.85/0.96  fof(f75,plain,(
% 1.85/0.96    v2_pre_topc(sK0)),
% 1.85/0.96    inference(cnf_transformation,[],[f55])).
% 1.85/0.96  
% 1.85/0.96  fof(f76,plain,(
% 1.85/0.96    l1_pre_topc(sK0)),
% 1.85/0.96    inference(cnf_transformation,[],[f55])).
% 1.85/0.96  
% 1.85/0.96  fof(f82,plain,(
% 1.85/0.96    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.85/0.96    inference(cnf_transformation,[],[f55])).
% 1.85/0.96  
% 1.85/0.96  fof(f87,plain,(
% 1.85/0.96    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.85/0.96    inference(cnf_transformation,[],[f55])).
% 1.85/0.96  
% 1.85/0.96  fof(f90,plain,(
% 1.85/0.96    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 1.85/0.96    inference(cnf_transformation,[],[f55])).
% 1.85/0.96  
% 1.85/0.96  fof(f72,plain,(
% 1.85/0.96    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.85/0.96    inference(cnf_transformation,[],[f46])).
% 1.85/0.96  
% 1.85/0.96  fof(f96,plain,(
% 1.85/0.96    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.85/0.96    inference(equality_resolution,[],[f72])).
% 1.85/0.96  
% 1.85/0.96  fof(f13,axiom,(
% 1.85/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 1.85/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/0.96  
% 1.85/0.96  fof(f37,plain,(
% 1.85/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.85/0.96    inference(ennf_transformation,[],[f13])).
% 1.85/0.96  
% 1.85/0.96  fof(f38,plain,(
% 1.85/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.85/0.96    inference(flattening,[],[f37])).
% 1.85/0.96  
% 1.85/0.96  fof(f71,plain,(
% 1.85/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.85/0.96    inference(cnf_transformation,[],[f38])).
% 1.85/0.96  
% 1.85/0.96  fof(f94,plain,(
% 1.85/0.96    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.85/0.96    inference(equality_resolution,[],[f71])).
% 1.85/0.96  
% 1.85/0.96  fof(f6,axiom,(
% 1.85/0.96    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.85/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/0.96  
% 1.85/0.96  fof(f25,plain,(
% 1.85/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.85/0.96    inference(ennf_transformation,[],[f6])).
% 1.85/0.96  
% 1.85/0.96  fof(f26,plain,(
% 1.85/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.85/0.96    inference(flattening,[],[f25])).
% 1.85/0.96  
% 1.85/0.96  fof(f61,plain,(
% 1.85/0.96    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.85/0.96    inference(cnf_transformation,[],[f26])).
% 1.85/0.96  
% 1.85/0.96  cnf(c_12,plain,
% 1.85/0.96      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 1.85/0.96      inference(cnf_transformation,[],[f68]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_1499,plain,
% 1.85/0.96      ( m1_pre_topc(X0_53,X0_53) | ~ l1_pre_topc(X0_53) ),
% 1.85/0.96      inference(subtyping,[status(esa)],[c_12]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_2082,plain,
% 1.85/0.96      ( m1_pre_topc(X0_53,X0_53) = iProver_top
% 1.85/0.96      | l1_pre_topc(X0_53) != iProver_top ),
% 1.85/0.96      inference(predicate_to_equality,[status(thm)],[c_1499]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_23,negated_conjecture,
% 1.85/0.96      ( m1_pre_topc(sK3,sK1) ),
% 1.85/0.96      inference(cnf_transformation,[],[f85]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_1491,negated_conjecture,
% 1.85/0.96      ( m1_pre_topc(sK3,sK1) ),
% 1.85/0.96      inference(subtyping,[status(esa)],[c_23]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_2089,plain,
% 1.85/0.96      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 1.85/0.96      inference(predicate_to_equality,[status(thm)],[c_1491]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_13,plain,
% 1.85/0.96      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 1.85/0.96      | ~ m1_pre_topc(X0,X2)
% 1.85/0.96      | ~ m1_pre_topc(X0,X1)
% 1.85/0.96      | ~ m1_pre_topc(X1,X2)
% 1.85/0.96      | ~ v2_pre_topc(X2)
% 1.85/0.96      | ~ l1_pre_topc(X2) ),
% 1.85/0.96      inference(cnf_transformation,[],[f70]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_1498,plain,
% 1.85/0.96      ( r1_tarski(u1_struct_0(X0_53),u1_struct_0(X1_53))
% 1.85/0.96      | ~ m1_pre_topc(X0_53,X2_53)
% 1.85/0.96      | ~ m1_pre_topc(X1_53,X2_53)
% 1.85/0.96      | ~ m1_pre_topc(X0_53,X1_53)
% 1.85/0.96      | ~ v2_pre_topc(X2_53)
% 1.85/0.96      | ~ l1_pre_topc(X2_53) ),
% 1.85/0.96      inference(subtyping,[status(esa)],[c_13]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_2083,plain,
% 1.85/0.96      ( r1_tarski(u1_struct_0(X0_53),u1_struct_0(X1_53)) = iProver_top
% 1.85/0.96      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 1.85/0.96      | m1_pre_topc(X1_53,X2_53) != iProver_top
% 1.85/0.96      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 1.85/0.96      | v2_pre_topc(X2_53) != iProver_top
% 1.85/0.96      | l1_pre_topc(X2_53) != iProver_top ),
% 1.85/0.96      inference(predicate_to_equality,[status(thm)],[c_1498]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_3032,plain,
% 1.85/0.96      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_53)) = iProver_top
% 1.85/0.96      | m1_pre_topc(X0_53,sK1) != iProver_top
% 1.85/0.96      | m1_pre_topc(sK3,X0_53) != iProver_top
% 1.85/0.96      | v2_pre_topc(sK1) != iProver_top
% 1.85/0.96      | l1_pre_topc(sK1) != iProver_top ),
% 1.85/0.96      inference(superposition,[status(thm)],[c_2089,c_2083]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_30,negated_conjecture,
% 1.85/0.96      ( v2_pre_topc(sK1) ),
% 1.85/0.96      inference(cnf_transformation,[],[f78]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_39,plain,
% 1.85/0.96      ( v2_pre_topc(sK1) = iProver_top ),
% 1.85/0.96      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_29,negated_conjecture,
% 1.85/0.96      ( l1_pre_topc(sK1) ),
% 1.85/0.96      inference(cnf_transformation,[],[f79]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_40,plain,
% 1.85/0.96      ( l1_pre_topc(sK1) = iProver_top ),
% 1.85/0.96      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_3104,plain,
% 1.85/0.96      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_53)) = iProver_top
% 1.85/0.96      | m1_pre_topc(X0_53,sK1) != iProver_top
% 1.85/0.96      | m1_pre_topc(sK3,X0_53) != iProver_top ),
% 1.85/0.96      inference(global_propositional_subsumption,
% 1.85/0.96                [status(thm)],
% 1.85/0.96                [c_3032,c_39,c_40]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_19,negated_conjecture,
% 1.85/0.96      ( r1_tmap_1(sK1,sK0,sK2,sK4)
% 1.85/0.96      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.85/0.96      inference(cnf_transformation,[],[f89]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_1495,negated_conjecture,
% 1.85/0.96      ( r1_tmap_1(sK1,sK0,sK2,sK4)
% 1.85/0.96      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.85/0.96      inference(subtyping,[status(esa)],[c_19]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_2086,plain,
% 1.85/0.96      ( r1_tmap_1(sK1,sK0,sK2,sK4) = iProver_top
% 1.85/0.96      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
% 1.85/0.96      inference(predicate_to_equality,[status(thm)],[c_1495]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_20,negated_conjecture,
% 1.85/0.96      ( sK4 = sK5 ),
% 1.85/0.96      inference(cnf_transformation,[],[f88]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_1494,negated_conjecture,
% 1.85/0.96      ( sK4 = sK5 ),
% 1.85/0.96      inference(subtyping,[status(esa)],[c_20]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_2144,plain,
% 1.85/0.96      ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
% 1.85/0.96      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
% 1.85/0.96      inference(light_normalisation,[status(thm)],[c_2086,c_1494]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_27,negated_conjecture,
% 1.85/0.96      ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 1.85/0.96      inference(cnf_transformation,[],[f81]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_16,plain,
% 1.85/0.96      ( r1_tmap_1(X0,X1,X2,X3)
% 1.85/0.96      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.85/0.96      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.85/0.96      | ~ m1_connsp_2(X5,X0,X3)
% 1.85/0.96      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.85/0.96      | ~ m1_pre_topc(X4,X0)
% 1.85/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/0.96      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.85/0.96      | ~ v1_funct_1(X2)
% 1.85/0.96      | ~ v2_pre_topc(X1)
% 1.85/0.96      | ~ v2_pre_topc(X0)
% 1.85/0.96      | v2_struct_0(X1)
% 1.85/0.96      | v2_struct_0(X0)
% 1.85/0.96      | v2_struct_0(X4)
% 1.85/0.96      | ~ l1_pre_topc(X1)
% 1.85/0.96      | ~ l1_pre_topc(X0) ),
% 1.85/0.96      inference(cnf_transformation,[],[f95]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_0,plain,
% 1.85/0.96      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.85/0.96      inference(cnf_transformation,[],[f56]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_7,plain,
% 1.85/0.96      ( m1_connsp_2(X0,X1,X2)
% 1.85/0.96      | ~ v3_pre_topc(X0,X1)
% 1.85/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.85/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.85/0.96      | ~ r2_hidden(X2,X0)
% 1.85/0.96      | ~ v2_pre_topc(X1)
% 1.85/0.96      | v2_struct_0(X1)
% 1.85/0.96      | ~ l1_pre_topc(X1) ),
% 1.85/0.96      inference(cnf_transformation,[],[f63]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_10,plain,
% 1.85/0.96      ( ~ v1_tsep_1(X0,X1)
% 1.85/0.96      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.85/0.96      | ~ m1_pre_topc(X0,X1)
% 1.85/0.96      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.85/0.96      | ~ v2_pre_topc(X1)
% 1.85/0.96      | ~ l1_pre_topc(X1) ),
% 1.85/0.96      inference(cnf_transformation,[],[f93]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_11,plain,
% 1.85/0.96      ( ~ m1_pre_topc(X0,X1)
% 1.85/0.96      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.85/0.96      | ~ l1_pre_topc(X1) ),
% 1.85/0.96      inference(cnf_transformation,[],[f67]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_193,plain,
% 1.85/0.96      ( ~ m1_pre_topc(X0,X1)
% 1.85/0.96      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.85/0.96      | ~ v1_tsep_1(X0,X1)
% 1.85/0.96      | ~ v2_pre_topc(X1)
% 1.85/0.96      | ~ l1_pre_topc(X1) ),
% 1.85/0.96      inference(global_propositional_subsumption,
% 1.85/0.96                [status(thm)],
% 1.85/0.96                [c_10,c_11]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_194,plain,
% 1.85/0.96      ( ~ v1_tsep_1(X0,X1)
% 1.85/0.96      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.85/0.96      | ~ m1_pre_topc(X0,X1)
% 1.85/0.96      | ~ v2_pre_topc(X1)
% 1.85/0.96      | ~ l1_pre_topc(X1) ),
% 1.85/0.96      inference(renaming,[status(thm)],[c_193]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_24,negated_conjecture,
% 1.85/0.96      ( v1_tsep_1(sK3,sK1) ),
% 1.85/0.96      inference(cnf_transformation,[],[f84]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_488,plain,
% 1.85/0.96      ( v3_pre_topc(u1_struct_0(X0),X1)
% 1.85/0.96      | ~ m1_pre_topc(X0,X1)
% 1.85/0.96      | ~ v2_pre_topc(X1)
% 1.85/0.96      | ~ l1_pre_topc(X1)
% 1.85/0.96      | sK1 != X1
% 1.85/0.96      | sK3 != X0 ),
% 1.85/0.96      inference(resolution_lifted,[status(thm)],[c_194,c_24]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_489,plain,
% 1.85/0.96      ( v3_pre_topc(u1_struct_0(sK3),sK1)
% 1.85/0.96      | ~ m1_pre_topc(sK3,sK1)
% 1.85/0.96      | ~ v2_pre_topc(sK1)
% 1.85/0.96      | ~ l1_pre_topc(sK1) ),
% 1.85/0.96      inference(unflattening,[status(thm)],[c_488]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_491,plain,
% 1.85/0.96      ( v3_pre_topc(u1_struct_0(sK3),sK1) ),
% 1.85/0.96      inference(global_propositional_subsumption,
% 1.85/0.96                [status(thm)],
% 1.85/0.96                [c_489,c_30,c_29,c_23]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_501,plain,
% 1.85/0.96      ( m1_connsp_2(X0,X1,X2)
% 1.85/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.85/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.85/0.96      | ~ r2_hidden(X2,X0)
% 1.85/0.96      | ~ v2_pre_topc(X1)
% 1.85/0.96      | v2_struct_0(X1)
% 1.85/0.96      | ~ l1_pre_topc(X1)
% 1.85/0.96      | u1_struct_0(sK3) != X0
% 1.85/0.96      | sK1 != X1 ),
% 1.85/0.96      inference(resolution_lifted,[status(thm)],[c_7,c_491]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_502,plain,
% 1.85/0.96      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
% 1.85/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.85/0.96      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/0.96      | ~ r2_hidden(X0,u1_struct_0(sK3))
% 1.85/0.96      | ~ v2_pre_topc(sK1)
% 1.85/0.96      | v2_struct_0(sK1)
% 1.85/0.96      | ~ l1_pre_topc(sK1) ),
% 1.85/0.96      inference(unflattening,[status(thm)],[c_501]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_31,negated_conjecture,
% 1.85/0.96      ( ~ v2_struct_0(sK1) ),
% 1.85/0.96      inference(cnf_transformation,[],[f77]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_506,plain,
% 1.85/0.96      ( ~ r2_hidden(X0,u1_struct_0(sK3))
% 1.85/0.96      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.85/0.96      | m1_connsp_2(u1_struct_0(sK3),sK1,X0) ),
% 1.85/0.96      inference(global_propositional_subsumption,
% 1.85/0.96                [status(thm)],
% 1.85/0.96                [c_502,c_31,c_30,c_29]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_507,plain,
% 1.85/0.96      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
% 1.85/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.85/0.96      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/0.96      | ~ r2_hidden(X0,u1_struct_0(sK3)) ),
% 1.85/0.96      inference(renaming,[status(thm)],[c_506]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_1,plain,
% 1.85/0.96      ( m1_subset_1(X0,X1)
% 1.85/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.85/0.96      | ~ r2_hidden(X0,X2) ),
% 1.85/0.96      inference(cnf_transformation,[],[f57]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_520,plain,
% 1.85/0.96      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
% 1.85/0.96      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/0.96      | ~ r2_hidden(X0,u1_struct_0(sK3)) ),
% 1.85/0.96      inference(forward_subsumption_resolution,[status(thm)],[c_507,c_1]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_547,plain,
% 1.85/0.96      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
% 1.85/0.96      | ~ m1_subset_1(X1,X2)
% 1.85/0.96      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/0.96      | v1_xboole_0(X2)
% 1.85/0.96      | X0 != X1
% 1.85/0.96      | u1_struct_0(sK3) != X2 ),
% 1.85/0.96      inference(resolution_lifted,[status(thm)],[c_0,c_520]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_548,plain,
% 1.85/0.96      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
% 1.85/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.85/0.96      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/0.96      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.85/0.96      inference(unflattening,[status(thm)],[c_547]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_632,plain,
% 1.85/0.96      ( r1_tmap_1(X0,X1,X2,X3)
% 1.85/0.96      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.85/0.96      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.85/0.96      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.85/0.96      | ~ m1_pre_topc(X4,X0)
% 1.85/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/0.96      | ~ m1_subset_1(X6,u1_struct_0(sK3))
% 1.85/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/0.96      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.85/0.96      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/0.96      | ~ v1_funct_1(X2)
% 1.85/0.96      | ~ v2_pre_topc(X0)
% 1.85/0.96      | ~ v2_pre_topc(X1)
% 1.85/0.96      | v2_struct_0(X0)
% 1.85/0.96      | v2_struct_0(X1)
% 1.85/0.96      | v2_struct_0(X4)
% 1.85/0.96      | ~ l1_pre_topc(X0)
% 1.85/0.96      | ~ l1_pre_topc(X1)
% 1.85/0.96      | v1_xboole_0(u1_struct_0(sK3))
% 1.85/0.96      | X6 != X3
% 1.85/0.96      | u1_struct_0(sK3) != X5
% 1.85/0.96      | sK1 != X0 ),
% 1.85/0.96      inference(resolution_lifted,[status(thm)],[c_16,c_548]) ).
% 1.85/0.96  
% 1.85/0.96  cnf(c_633,plain,
% 1.85/0.96      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.85/0.96      | r1_tmap_1(sK1,X1,X2,X3)
% 1.85/0.96      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.85/0.96      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.85/0.96      | ~ m1_pre_topc(X0,sK1)
% 1.85/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/0.96      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.85/0.96      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.85/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.85/0.96      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/0.97      | ~ v1_funct_1(X2)
% 1.85/0.97      | ~ v2_pre_topc(X1)
% 1.85/0.97      | ~ v2_pre_topc(sK1)
% 1.85/0.97      | v2_struct_0(X1)
% 1.85/0.97      | v2_struct_0(X0)
% 1.85/0.97      | v2_struct_0(sK1)
% 1.85/0.97      | ~ l1_pre_topc(X1)
% 1.85/0.97      | ~ l1_pre_topc(sK1)
% 1.85/0.97      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.85/0.97      inference(unflattening,[status(thm)],[c_632]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_637,plain,
% 1.85/0.97      ( ~ l1_pre_topc(X1)
% 1.85/0.97      | ~ v2_pre_topc(X1)
% 1.85/0.97      | ~ v1_funct_1(X2)
% 1.85/0.97      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/0.97      | ~ m1_pre_topc(X0,sK1)
% 1.85/0.97      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.85/0.97      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.85/0.97      | r1_tmap_1(sK1,X1,X2,X3)
% 1.85/0.97      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.85/0.97      | v2_struct_0(X1)
% 1.85/0.97      | v2_struct_0(X0)
% 1.85/0.97      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.85/0.97      inference(global_propositional_subsumption,
% 1.85/0.97                [status(thm)],
% 1.85/0.97                [c_633,c_31,c_30,c_29]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_638,plain,
% 1.85/0.97      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.85/0.97      | r1_tmap_1(sK1,X1,X2,X3)
% 1.85/0.97      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.85/0.97      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.85/0.97      | ~ m1_pre_topc(X0,sK1)
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.85/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.85/0.97      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/0.97      | ~ v1_funct_1(X2)
% 1.85/0.97      | ~ v2_pre_topc(X1)
% 1.85/0.97      | v2_struct_0(X0)
% 1.85/0.97      | v2_struct_0(X1)
% 1.85/0.97      | ~ l1_pre_topc(X1)
% 1.85/0.97      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.85/0.97      inference(renaming,[status(thm)],[c_637]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_531,plain,
% 1.85/0.97      ( ~ m1_subset_1(X0,X1)
% 1.85/0.97      | m1_subset_1(X2,X3)
% 1.85/0.97      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
% 1.85/0.97      | v1_xboole_0(X1)
% 1.85/0.97      | X2 != X0
% 1.85/0.97      | X4 != X1 ),
% 1.85/0.97      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_532,plain,
% 1.85/0.97      ( ~ m1_subset_1(X0,X1)
% 1.85/0.97      | m1_subset_1(X0,X2)
% 1.85/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.85/0.97      | v1_xboole_0(X1) ),
% 1.85/0.97      inference(unflattening,[status(thm)],[c_531]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_673,plain,
% 1.85/0.97      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.85/0.97      | r1_tmap_1(sK1,X1,X2,X3)
% 1.85/0.97      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.85/0.97      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.85/0.97      | ~ m1_pre_topc(X0,sK1)
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.85/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.85/0.97      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/0.97      | ~ v1_funct_1(X2)
% 1.85/0.97      | ~ v2_pre_topc(X1)
% 1.85/0.97      | v2_struct_0(X0)
% 1.85/0.97      | v2_struct_0(X1)
% 1.85/0.97      | ~ l1_pre_topc(X1)
% 1.85/0.97      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.85/0.97      inference(forward_subsumption_resolution,
% 1.85/0.97                [status(thm)],
% 1.85/0.97                [c_638,c_532]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_925,plain,
% 1.85/0.97      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.85/0.97      | r1_tmap_1(sK1,X1,X2,X3)
% 1.85/0.97      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.85/0.97      | ~ m1_pre_topc(X0,sK1)
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.85/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.85/0.97      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/0.97      | ~ v1_funct_1(X2)
% 1.85/0.97      | ~ v2_pre_topc(X1)
% 1.85/0.97      | v2_struct_0(X1)
% 1.85/0.97      | v2_struct_0(X0)
% 1.85/0.97      | ~ l1_pre_topc(X1)
% 1.85/0.97      | v1_xboole_0(u1_struct_0(sK3))
% 1.85/0.97      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.85/0.97      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.85/0.97      | sK2 != X2 ),
% 1.85/0.97      inference(resolution_lifted,[status(thm)],[c_27,c_673]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_926,plain,
% 1.85/0.97      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
% 1.85/0.97      | r1_tmap_1(sK1,X1,sK2,X2)
% 1.85/0.97      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.85/0.97      | ~ m1_pre_topc(X0,sK1)
% 1.85/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.85/0.97      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.85/0.97      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.85/0.97      | ~ v1_funct_1(sK2)
% 1.85/0.97      | ~ v2_pre_topc(X1)
% 1.85/0.97      | v2_struct_0(X0)
% 1.85/0.97      | v2_struct_0(X1)
% 1.85/0.97      | ~ l1_pre_topc(X1)
% 1.85/0.97      | v1_xboole_0(u1_struct_0(sK3))
% 1.85/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.85/0.97      inference(unflattening,[status(thm)],[c_925]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_28,negated_conjecture,
% 1.85/0.97      ( v1_funct_1(sK2) ),
% 1.85/0.97      inference(cnf_transformation,[],[f80]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_930,plain,
% 1.85/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.85/0.97      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/0.97      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.85/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.85/0.97      | ~ m1_pre_topc(X0,sK1)
% 1.85/0.97      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.85/0.97      | r1_tmap_1(sK1,X1,sK2,X2)
% 1.85/0.97      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
% 1.85/0.97      | ~ v2_pre_topc(X1)
% 1.85/0.97      | v2_struct_0(X0)
% 1.85/0.97      | v2_struct_0(X1)
% 1.85/0.97      | ~ l1_pre_topc(X1)
% 1.85/0.97      | v1_xboole_0(u1_struct_0(sK3))
% 1.85/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.85/0.97      inference(global_propositional_subsumption,
% 1.85/0.97                [status(thm)],
% 1.85/0.97                [c_926,c_28]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_931,plain,
% 1.85/0.97      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
% 1.85/0.97      | r1_tmap_1(sK1,X1,sK2,X2)
% 1.85/0.97      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.85/0.97      | ~ m1_pre_topc(X0,sK1)
% 1.85/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.85/0.97      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.85/0.97      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.85/0.97      | ~ v2_pre_topc(X1)
% 1.85/0.97      | v2_struct_0(X0)
% 1.85/0.97      | v2_struct_0(X1)
% 1.85/0.97      | ~ l1_pre_topc(X1)
% 1.85/0.97      | v1_xboole_0(u1_struct_0(sK3))
% 1.85/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.85/0.97      inference(renaming,[status(thm)],[c_930]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_1479,plain,
% 1.85/0.97      ( ~ r1_tmap_1(X0_53,X1_53,k2_tmap_1(sK1,X1_53,sK2,X0_53),X0_54)
% 1.85/0.97      | r1_tmap_1(sK1,X1_53,sK2,X0_54)
% 1.85/0.97      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_53))
% 1.85/0.97      | ~ m1_pre_topc(X0_53,sK1)
% 1.85/0.97      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 1.85/0.97      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 1.85/0.97      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1_53))))
% 1.85/0.97      | ~ v2_pre_topc(X1_53)
% 1.85/0.97      | v2_struct_0(X0_53)
% 1.85/0.97      | v2_struct_0(X1_53)
% 1.85/0.97      | ~ l1_pre_topc(X1_53)
% 1.85/0.97      | v1_xboole_0(u1_struct_0(sK3))
% 1.85/0.97      | u1_struct_0(X1_53) != u1_struct_0(sK0) ),
% 1.85/0.97      inference(subtyping,[status(esa)],[c_931]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_1503,plain,
% 1.85/0.97      ( ~ r1_tmap_1(X0_53,X1_53,k2_tmap_1(sK1,X1_53,sK2,X0_53),X0_54)
% 1.85/0.97      | r1_tmap_1(sK1,X1_53,sK2,X0_54)
% 1.85/0.97      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_53))
% 1.85/0.97      | ~ m1_pre_topc(X0_53,sK1)
% 1.85/0.97      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 1.85/0.97      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 1.85/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1_53))))
% 1.85/0.97      | ~ v2_pre_topc(X1_53)
% 1.85/0.97      | v2_struct_0(X0_53)
% 1.85/0.97      | v2_struct_0(X1_53)
% 1.85/0.97      | ~ l1_pre_topc(X1_53)
% 1.85/0.97      | u1_struct_0(X1_53) != u1_struct_0(sK0)
% 1.85/0.97      | ~ sP0_iProver_split ),
% 1.85/0.97      inference(splitting,
% 1.85/0.97                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.85/0.97                [c_1479]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2102,plain,
% 1.85/0.97      ( u1_struct_0(X0_53) != u1_struct_0(sK0)
% 1.85/0.97      | r1_tmap_1(X1_53,X0_53,k2_tmap_1(sK1,X0_53,sK2,X1_53),X0_54) != iProver_top
% 1.85/0.97      | r1_tmap_1(sK1,X0_53,sK2,X0_54) = iProver_top
% 1.85/0.97      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X1_53)) != iProver_top
% 1.85/0.97      | m1_pre_topc(X1_53,sK1) != iProver_top
% 1.85/0.97      | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
% 1.85/0.97      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 1.85/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_53)))) != iProver_top
% 1.85/0.97      | v2_pre_topc(X0_53) != iProver_top
% 1.85/0.97      | v2_struct_0(X0_53) = iProver_top
% 1.85/0.97      | v2_struct_0(X1_53) = iProver_top
% 1.85/0.97      | l1_pre_topc(X0_53) != iProver_top
% 1.85/0.97      | sP0_iProver_split != iProver_top ),
% 1.85/0.97      inference(predicate_to_equality,[status(thm)],[c_1503]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_25,negated_conjecture,
% 1.85/0.97      ( ~ v2_struct_0(sK3) ),
% 1.85/0.97      inference(cnf_transformation,[],[f83]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_44,plain,
% 1.85/0.97      ( v2_struct_0(sK3) != iProver_top ),
% 1.85/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_46,plain,
% 1.85/0.97      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 1.85/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_1504,plain,
% 1.85/0.97      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/0.97      | v1_xboole_0(u1_struct_0(sK3))
% 1.85/0.97      | sP0_iProver_split ),
% 1.85/0.97      inference(splitting,
% 1.85/0.97                [splitting(split),new_symbols(definition,[])],
% 1.85/0.97                [c_1479]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_1548,plain,
% 1.85/0.97      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.85/0.97      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 1.85/0.97      | sP0_iProver_split = iProver_top ),
% 1.85/0.97      inference(predicate_to_equality,[status(thm)],[c_1504]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_1549,plain,
% 1.85/0.97      ( u1_struct_0(X0_53) != u1_struct_0(sK0)
% 1.85/0.97      | r1_tmap_1(X1_53,X0_53,k2_tmap_1(sK1,X0_53,sK2,X1_53),X0_54) != iProver_top
% 1.85/0.97      | r1_tmap_1(sK1,X0_53,sK2,X0_54) = iProver_top
% 1.85/0.97      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X1_53)) != iProver_top
% 1.85/0.97      | m1_pre_topc(X1_53,sK1) != iProver_top
% 1.85/0.97      | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
% 1.85/0.97      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 1.85/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_53)))) != iProver_top
% 1.85/0.97      | v2_pre_topc(X0_53) != iProver_top
% 1.85/0.97      | v2_struct_0(X0_53) = iProver_top
% 1.85/0.97      | v2_struct_0(X1_53) = iProver_top
% 1.85/0.97      | l1_pre_topc(X0_53) != iProver_top
% 1.85/0.97      | sP0_iProver_split != iProver_top ),
% 1.85/0.97      inference(predicate_to_equality,[status(thm)],[c_1503]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_1500,plain,
% 1.85/0.97      ( ~ m1_pre_topc(X0_53,X1_53)
% 1.85/0.97      | m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X1_53)))
% 1.85/0.97      | ~ l1_pre_topc(X1_53) ),
% 1.85/0.97      inference(subtyping,[status(esa)],[c_11]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2327,plain,
% 1.85/0.97      ( ~ m1_pre_topc(sK3,sK1)
% 1.85/0.97      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/0.97      | ~ l1_pre_topc(sK1) ),
% 1.85/0.97      inference(instantiation,[status(thm)],[c_1500]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2328,plain,
% 1.85/0.97      ( m1_pre_topc(sK3,sK1) != iProver_top
% 1.85/0.97      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.85/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 1.85/0.97      inference(predicate_to_equality,[status(thm)],[c_2327]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2,plain,
% 1.85/0.97      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.85/0.97      inference(cnf_transformation,[],[f58]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_4,plain,
% 1.85/0.97      ( v2_struct_0(X0)
% 1.85/0.97      | ~ l1_struct_0(X0)
% 1.85/0.97      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.85/0.97      inference(cnf_transformation,[],[f60]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_447,plain,
% 1.85/0.97      ( v2_struct_0(X0)
% 1.85/0.97      | ~ l1_pre_topc(X0)
% 1.85/0.97      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.85/0.97      inference(resolution,[status(thm)],[c_2,c_4]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_1482,plain,
% 1.85/0.97      ( v2_struct_0(X0_53)
% 1.85/0.97      | ~ l1_pre_topc(X0_53)
% 1.85/0.97      | ~ v1_xboole_0(u1_struct_0(X0_53)) ),
% 1.85/0.97      inference(subtyping,[status(esa)],[c_447]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2498,plain,
% 1.85/0.97      ( v2_struct_0(sK3)
% 1.85/0.97      | ~ l1_pre_topc(sK3)
% 1.85/0.97      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.85/0.97      inference(instantiation,[status(thm)],[c_1482]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2499,plain,
% 1.85/0.97      ( v2_struct_0(sK3) = iProver_top
% 1.85/0.97      | l1_pre_topc(sK3) != iProver_top
% 1.85/0.97      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 1.85/0.97      inference(predicate_to_equality,[status(thm)],[c_2498]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_3,plain,
% 1.85/0.97      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.85/0.97      inference(cnf_transformation,[],[f59]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_1502,plain,
% 1.85/0.97      ( ~ m1_pre_topc(X0_53,X1_53)
% 1.85/0.97      | ~ l1_pre_topc(X1_53)
% 1.85/0.97      | l1_pre_topc(X0_53) ),
% 1.85/0.97      inference(subtyping,[status(esa)],[c_3]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2079,plain,
% 1.85/0.97      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 1.85/0.97      | l1_pre_topc(X1_53) != iProver_top
% 1.85/0.97      | l1_pre_topc(X0_53) = iProver_top ),
% 1.85/0.97      inference(predicate_to_equality,[status(thm)],[c_1502]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2518,plain,
% 1.85/0.97      ( l1_pre_topc(sK1) != iProver_top
% 1.85/0.97      | l1_pre_topc(sK3) = iProver_top ),
% 1.85/0.97      inference(superposition,[status(thm)],[c_2089,c_2079]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2768,plain,
% 1.85/0.97      ( l1_pre_topc(X0_53) != iProver_top
% 1.85/0.97      | v2_struct_0(X1_53) = iProver_top
% 1.85/0.97      | v2_struct_0(X0_53) = iProver_top
% 1.85/0.97      | v2_pre_topc(X0_53) != iProver_top
% 1.85/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_53)))) != iProver_top
% 1.85/0.97      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 1.85/0.97      | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
% 1.85/0.97      | m1_pre_topc(X1_53,sK1) != iProver_top
% 1.85/0.97      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X1_53)) != iProver_top
% 1.85/0.97      | r1_tmap_1(sK1,X0_53,sK2,X0_54) = iProver_top
% 1.85/0.97      | r1_tmap_1(X1_53,X0_53,k2_tmap_1(sK1,X0_53,sK2,X1_53),X0_54) != iProver_top
% 1.85/0.97      | u1_struct_0(X0_53) != u1_struct_0(sK0) ),
% 1.85/0.97      inference(global_propositional_subsumption,
% 1.85/0.97                [status(thm)],
% 1.85/0.97                [c_2102,c_40,c_44,c_46,c_1548,c_1549,c_2328,c_2499,
% 1.85/0.97                 c_2518]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2769,plain,
% 1.85/0.97      ( u1_struct_0(X0_53) != u1_struct_0(sK0)
% 1.85/0.97      | r1_tmap_1(X1_53,X0_53,k2_tmap_1(sK1,X0_53,sK2,X1_53),X0_54) != iProver_top
% 1.85/0.97      | r1_tmap_1(sK1,X0_53,sK2,X0_54) = iProver_top
% 1.85/0.97      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X1_53)) != iProver_top
% 1.85/0.97      | m1_pre_topc(X1_53,sK1) != iProver_top
% 1.85/0.97      | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
% 1.85/0.97      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 1.85/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_53)))) != iProver_top
% 1.85/0.97      | v2_pre_topc(X0_53) != iProver_top
% 1.85/0.97      | v2_struct_0(X1_53) = iProver_top
% 1.85/0.97      | v2_struct_0(X0_53) = iProver_top
% 1.85/0.97      | l1_pre_topc(X0_53) != iProver_top ),
% 1.85/0.97      inference(renaming,[status(thm)],[c_2768]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2786,plain,
% 1.85/0.97      ( r1_tmap_1(X0_53,sK0,k2_tmap_1(sK1,sK0,sK2,X0_53),X0_54) != iProver_top
% 1.85/0.97      | r1_tmap_1(sK1,sK0,sK2,X0_54) = iProver_top
% 1.85/0.97      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_53)) != iProver_top
% 1.85/0.97      | m1_pre_topc(X0_53,sK1) != iProver_top
% 1.85/0.97      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 1.85/0.97      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 1.85/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 1.85/0.97      | v2_pre_topc(sK0) != iProver_top
% 1.85/0.97      | v2_struct_0(X0_53) = iProver_top
% 1.85/0.97      | v2_struct_0(sK0) = iProver_top
% 1.85/0.97      | l1_pre_topc(sK0) != iProver_top ),
% 1.85/0.97      inference(equality_resolution,[status(thm)],[c_2769]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_34,negated_conjecture,
% 1.85/0.97      ( ~ v2_struct_0(sK0) ),
% 1.85/0.97      inference(cnf_transformation,[],[f74]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_35,plain,
% 1.85/0.97      ( v2_struct_0(sK0) != iProver_top ),
% 1.85/0.97      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_33,negated_conjecture,
% 1.85/0.97      ( v2_pre_topc(sK0) ),
% 1.85/0.97      inference(cnf_transformation,[],[f75]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_36,plain,
% 1.85/0.97      ( v2_pre_topc(sK0) = iProver_top ),
% 1.85/0.97      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_32,negated_conjecture,
% 1.85/0.97      ( l1_pre_topc(sK0) ),
% 1.85/0.97      inference(cnf_transformation,[],[f76]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_37,plain,
% 1.85/0.97      ( l1_pre_topc(sK0) = iProver_top ),
% 1.85/0.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_26,negated_conjecture,
% 1.85/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 1.85/0.97      inference(cnf_transformation,[],[f82]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_43,plain,
% 1.85/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 1.85/0.97      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2854,plain,
% 1.85/0.97      ( r1_tmap_1(X0_53,sK0,k2_tmap_1(sK1,sK0,sK2,X0_53),X0_54) != iProver_top
% 1.85/0.97      | r1_tmap_1(sK1,sK0,sK2,X0_54) = iProver_top
% 1.85/0.97      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_53)) != iProver_top
% 1.85/0.97      | m1_pre_topc(X0_53,sK1) != iProver_top
% 1.85/0.97      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 1.85/0.97      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 1.85/0.97      | v2_struct_0(X0_53) = iProver_top ),
% 1.85/0.97      inference(global_propositional_subsumption,
% 1.85/0.97                [status(thm)],
% 1.85/0.97                [c_2786,c_35,c_36,c_37,c_43]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2867,plain,
% 1.85/0.97      ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
% 1.85/0.97      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 1.85/0.97      | m1_pre_topc(sK3,sK1) != iProver_top
% 1.85/0.97      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 1.85/0.97      | v2_struct_0(sK3) = iProver_top ),
% 1.85/0.97      inference(superposition,[status(thm)],[c_2144,c_2854]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_21,negated_conjecture,
% 1.85/0.97      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 1.85/0.97      inference(cnf_transformation,[],[f87]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_48,plain,
% 1.85/0.97      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 1.85/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2870,plain,
% 1.85/0.97      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 1.85/0.97      | r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top ),
% 1.85/0.97      inference(global_propositional_subsumption,
% 1.85/0.97                [status(thm)],
% 1.85/0.97                [c_2867,c_44,c_46,c_48]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2871,plain,
% 1.85/0.97      ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
% 1.85/0.97      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
% 1.85/0.97      inference(renaming,[status(thm)],[c_2870]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_3114,plain,
% 1.85/0.97      ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
% 1.85/0.97      | m1_pre_topc(sK3,sK1) != iProver_top
% 1.85/0.97      | m1_pre_topc(sK3,sK3) != iProver_top ),
% 1.85/0.97      inference(superposition,[status(thm)],[c_3104,c_2871]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_38,plain,
% 1.85/0.97      ( v2_struct_0(sK1) != iProver_top ),
% 1.85/0.97      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_18,negated_conjecture,
% 1.85/0.97      ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
% 1.85/0.97      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.85/0.97      inference(cnf_transformation,[],[f90]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_1496,negated_conjecture,
% 1.85/0.97      ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
% 1.85/0.97      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.85/0.97      inference(subtyping,[status(esa)],[c_18]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2085,plain,
% 1.85/0.97      ( r1_tmap_1(sK1,sK0,sK2,sK4) != iProver_top
% 1.85/0.97      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
% 1.85/0.97      inference(predicate_to_equality,[status(thm)],[c_1496]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2161,plain,
% 1.85/0.97      ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
% 1.85/0.97      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
% 1.85/0.97      inference(light_normalisation,[status(thm)],[c_2085,c_1494]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_1506,plain,( X0_54 = X0_54 ),theory(equality) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2319,plain,
% 1.85/0.97      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 1.85/0.97      inference(instantiation,[status(thm)],[c_1506]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2528,plain,
% 1.85/0.97      ( u1_struct_0(X0_53) = u1_struct_0(X0_53) ),
% 1.85/0.97      inference(instantiation,[status(thm)],[c_1506]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2706,plain,
% 1.85/0.97      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 1.85/0.97      inference(instantiation,[status(thm)],[c_2528]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_17,plain,
% 1.85/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.85/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.85/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.85/0.97      | ~ m1_connsp_2(X5,X0,X3)
% 1.85/0.97      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.85/0.97      | ~ m1_pre_topc(X4,X0)
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.85/0.97      | ~ v1_funct_1(X2)
% 1.85/0.97      | ~ v2_pre_topc(X1)
% 1.85/0.97      | ~ v2_pre_topc(X0)
% 1.85/0.97      | v2_struct_0(X1)
% 1.85/0.97      | v2_struct_0(X0)
% 1.85/0.97      | v2_struct_0(X4)
% 1.85/0.97      | ~ l1_pre_topc(X1)
% 1.85/0.97      | ~ l1_pre_topc(X0) ),
% 1.85/0.97      inference(cnf_transformation,[],[f96]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_15,plain,
% 1.85/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.85/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.85/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.85/0.97      | ~ m1_pre_topc(X4,X0)
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/0.97      | ~ v1_funct_1(X2)
% 1.85/0.97      | ~ v2_pre_topc(X1)
% 1.85/0.97      | ~ v2_pre_topc(X0)
% 1.85/0.97      | v2_struct_0(X1)
% 1.85/0.97      | v2_struct_0(X0)
% 1.85/0.97      | v2_struct_0(X4)
% 1.85/0.97      | ~ l1_pre_topc(X1)
% 1.85/0.97      | ~ l1_pre_topc(X0) ),
% 1.85/0.97      inference(cnf_transformation,[],[f94]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_182,plain,
% 1.85/0.97      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/0.97      | ~ m1_pre_topc(X4,X0)
% 1.85/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.85/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.85/0.97      | ~ r1_tmap_1(X0,X1,X2,X3)
% 1.85/0.97      | ~ v1_funct_1(X2)
% 1.85/0.97      | ~ v2_pre_topc(X1)
% 1.85/0.97      | ~ v2_pre_topc(X0)
% 1.85/0.97      | v2_struct_0(X1)
% 1.85/0.97      | v2_struct_0(X0)
% 1.85/0.97      | v2_struct_0(X4)
% 1.85/0.97      | ~ l1_pre_topc(X1)
% 1.85/0.97      | ~ l1_pre_topc(X0) ),
% 1.85/0.97      inference(global_propositional_subsumption,
% 1.85/0.97                [status(thm)],
% 1.85/0.97                [c_17,c_15]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_183,plain,
% 1.85/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.85/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.85/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.85/0.97      | ~ m1_pre_topc(X4,X0)
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/0.97      | ~ v1_funct_1(X2)
% 1.85/0.97      | ~ v2_pre_topc(X0)
% 1.85/0.97      | ~ v2_pre_topc(X1)
% 1.85/0.97      | v2_struct_0(X0)
% 1.85/0.97      | v2_struct_0(X1)
% 1.85/0.97      | v2_struct_0(X4)
% 1.85/0.97      | ~ l1_pre_topc(X0)
% 1.85/0.97      | ~ l1_pre_topc(X1) ),
% 1.85/0.97      inference(renaming,[status(thm)],[c_182]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_819,plain,
% 1.85/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.85/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.85/0.97      | ~ m1_pre_topc(X4,X0)
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/0.97      | ~ v1_funct_1(X2)
% 1.85/0.97      | ~ v2_pre_topc(X0)
% 1.85/0.97      | ~ v2_pre_topc(X1)
% 1.85/0.97      | v2_struct_0(X0)
% 1.85/0.97      | v2_struct_0(X1)
% 1.85/0.97      | v2_struct_0(X4)
% 1.85/0.97      | ~ l1_pre_topc(X0)
% 1.85/0.97      | ~ l1_pre_topc(X1)
% 1.85/0.97      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.85/0.97      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.85/0.97      | sK2 != X2 ),
% 1.85/0.97      inference(resolution_lifted,[status(thm)],[c_183,c_27]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_820,plain,
% 1.85/0.97      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.85/0.97      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.85/0.97      | ~ m1_pre_topc(X0,X2)
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.85/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.85/0.97      | ~ v1_funct_1(sK2)
% 1.85/0.97      | ~ v2_pre_topc(X2)
% 1.85/0.97      | ~ v2_pre_topc(X1)
% 1.85/0.97      | v2_struct_0(X2)
% 1.85/0.97      | v2_struct_0(X1)
% 1.85/0.97      | v2_struct_0(X0)
% 1.85/0.97      | ~ l1_pre_topc(X2)
% 1.85/0.97      | ~ l1_pre_topc(X1)
% 1.85/0.97      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.85/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.85/0.97      inference(unflattening,[status(thm)],[c_819]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_824,plain,
% 1.85/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/0.97      | ~ m1_pre_topc(X0,X2)
% 1.85/0.97      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.85/0.97      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.85/0.97      | ~ v2_pre_topc(X2)
% 1.85/0.97      | ~ v2_pre_topc(X1)
% 1.85/0.97      | v2_struct_0(X2)
% 1.85/0.97      | v2_struct_0(X1)
% 1.85/0.97      | v2_struct_0(X0)
% 1.85/0.97      | ~ l1_pre_topc(X2)
% 1.85/0.97      | ~ l1_pre_topc(X1)
% 1.85/0.97      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.85/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.85/0.97      inference(global_propositional_subsumption,
% 1.85/0.97                [status(thm)],
% 1.85/0.97                [c_820,c_28]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_825,plain,
% 1.85/0.97      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.85/0.97      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.85/0.97      | ~ m1_pre_topc(X0,X2)
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.85/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.85/0.97      | ~ v2_pre_topc(X1)
% 1.85/0.97      | ~ v2_pre_topc(X2)
% 1.85/0.97      | v2_struct_0(X0)
% 1.85/0.97      | v2_struct_0(X1)
% 1.85/0.97      | v2_struct_0(X2)
% 1.85/0.97      | ~ l1_pre_topc(X1)
% 1.85/0.97      | ~ l1_pre_topc(X2)
% 1.85/0.97      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.85/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.85/0.97      inference(renaming,[status(thm)],[c_824]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_5,plain,
% 1.85/0.97      ( ~ m1_pre_topc(X0,X1)
% 1.85/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.85/0.97      | m1_subset_1(X2,u1_struct_0(X1))
% 1.85/0.97      | v2_struct_0(X1)
% 1.85/0.97      | v2_struct_0(X0)
% 1.85/0.97      | ~ l1_pre_topc(X1) ),
% 1.85/0.97      inference(cnf_transformation,[],[f61]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_860,plain,
% 1.85/0.97      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.85/0.97      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.85/0.97      | ~ m1_pre_topc(X0,X2)
% 1.85/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.85/0.97      | ~ v2_pre_topc(X1)
% 1.85/0.97      | ~ v2_pre_topc(X2)
% 1.85/0.97      | v2_struct_0(X0)
% 1.85/0.97      | v2_struct_0(X1)
% 1.85/0.97      | v2_struct_0(X2)
% 1.85/0.97      | ~ l1_pre_topc(X1)
% 1.85/0.97      | ~ l1_pre_topc(X2)
% 1.85/0.97      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.85/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.85/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_825,c_5]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_1480,plain,
% 1.85/0.97      ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,sK2,X0_53),X0_54)
% 1.85/0.97      | ~ r1_tmap_1(X2_53,X1_53,sK2,X0_54)
% 1.85/0.97      | ~ m1_pre_topc(X0_53,X2_53)
% 1.85/0.97      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 1.85/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 1.85/0.97      | ~ v2_pre_topc(X1_53)
% 1.85/0.97      | ~ v2_pre_topc(X2_53)
% 1.85/0.97      | v2_struct_0(X0_53)
% 1.85/0.97      | v2_struct_0(X1_53)
% 1.85/0.97      | v2_struct_0(X2_53)
% 1.85/0.97      | ~ l1_pre_topc(X1_53)
% 1.85/0.97      | ~ l1_pre_topc(X2_53)
% 1.85/0.97      | u1_struct_0(X2_53) != u1_struct_0(sK1)
% 1.85/0.97      | u1_struct_0(X1_53) != u1_struct_0(sK0) ),
% 1.85/0.97      inference(subtyping,[status(esa)],[c_860]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_2708,plain,
% 1.85/0.97      ( r1_tmap_1(X0_53,sK0,k2_tmap_1(X1_53,sK0,sK2,X0_53),X0_54)
% 1.85/0.97      | ~ r1_tmap_1(X1_53,sK0,sK2,X0_54)
% 1.85/0.97      | ~ m1_pre_topc(X0_53,X1_53)
% 1.85/0.97      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 1.85/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(sK0))))
% 1.85/0.97      | ~ v2_pre_topc(X1_53)
% 1.85/0.97      | ~ v2_pre_topc(sK0)
% 1.85/0.97      | v2_struct_0(X0_53)
% 1.85/0.97      | v2_struct_0(X1_53)
% 1.85/0.97      | v2_struct_0(sK0)
% 1.85/0.97      | ~ l1_pre_topc(X1_53)
% 1.85/0.97      | ~ l1_pre_topc(sK0)
% 1.85/0.97      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 1.85/0.97      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.85/0.97      inference(instantiation,[status(thm)],[c_1480]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_3222,plain,
% 1.85/0.97      ( ~ r1_tmap_1(X0_53,sK0,sK2,sK5)
% 1.85/0.97      | r1_tmap_1(sK3,sK0,k2_tmap_1(X0_53,sK0,sK2,sK3),sK5)
% 1.85/0.97      | ~ m1_pre_topc(sK3,X0_53)
% 1.85/0.97      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.85/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK0))))
% 1.85/0.97      | ~ v2_pre_topc(X0_53)
% 1.85/0.97      | ~ v2_pre_topc(sK0)
% 1.85/0.97      | v2_struct_0(X0_53)
% 1.85/0.97      | v2_struct_0(sK0)
% 1.85/0.97      | v2_struct_0(sK3)
% 1.85/0.97      | ~ l1_pre_topc(X0_53)
% 1.85/0.97      | ~ l1_pre_topc(sK0)
% 1.85/0.97      | u1_struct_0(X0_53) != u1_struct_0(sK1)
% 1.85/0.97      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.85/0.97      inference(instantiation,[status(thm)],[c_2708]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_3223,plain,
% 1.85/0.97      ( u1_struct_0(X0_53) != u1_struct_0(sK1)
% 1.85/0.97      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 1.85/0.97      | r1_tmap_1(X0_53,sK0,sK2,sK5) != iProver_top
% 1.85/0.97      | r1_tmap_1(sK3,sK0,k2_tmap_1(X0_53,sK0,sK2,sK3),sK5) = iProver_top
% 1.85/0.97      | m1_pre_topc(sK3,X0_53) != iProver_top
% 1.85/0.97      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 1.85/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK0)))) != iProver_top
% 1.85/0.97      | v2_pre_topc(X0_53) != iProver_top
% 1.85/0.97      | v2_pre_topc(sK0) != iProver_top
% 1.85/0.97      | v2_struct_0(X0_53) = iProver_top
% 1.85/0.97      | v2_struct_0(sK0) = iProver_top
% 1.85/0.97      | v2_struct_0(sK3) = iProver_top
% 1.85/0.97      | l1_pre_topc(X0_53) != iProver_top
% 1.85/0.97      | l1_pre_topc(sK0) != iProver_top ),
% 1.85/0.97      inference(predicate_to_equality,[status(thm)],[c_3222]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_3225,plain,
% 1.85/0.97      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.85/0.97      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 1.85/0.97      | r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
% 1.85/0.97      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top
% 1.85/0.97      | m1_pre_topc(sK3,sK1) != iProver_top
% 1.85/0.97      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 1.85/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 1.85/0.97      | v2_pre_topc(sK1) != iProver_top
% 1.85/0.97      | v2_pre_topc(sK0) != iProver_top
% 1.85/0.97      | v2_struct_0(sK1) = iProver_top
% 1.85/0.97      | v2_struct_0(sK0) = iProver_top
% 1.85/0.97      | v2_struct_0(sK3) = iProver_top
% 1.85/0.97      | l1_pre_topc(sK1) != iProver_top
% 1.85/0.97      | l1_pre_topc(sK0) != iProver_top ),
% 1.85/0.97      inference(instantiation,[status(thm)],[c_3223]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_3289,plain,
% 1.85/0.97      ( m1_pre_topc(sK3,sK3) != iProver_top ),
% 1.85/0.97      inference(global_propositional_subsumption,
% 1.85/0.97                [status(thm)],
% 1.85/0.97                [c_3114,c_35,c_36,c_37,c_38,c_39,c_40,c_43,c_44,c_46,
% 1.85/0.97                 c_48,c_2161,c_2319,c_2706,c_3225]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(c_3294,plain,
% 1.85/0.97      ( l1_pre_topc(sK3) != iProver_top ),
% 1.85/0.97      inference(superposition,[status(thm)],[c_2082,c_3289]) ).
% 1.85/0.97  
% 1.85/0.97  cnf(contradiction,plain,
% 1.85/0.97      ( $false ),
% 1.85/0.97      inference(minisat,[status(thm)],[c_3294,c_2518,c_40]) ).
% 1.85/0.97  
% 1.85/0.97  
% 1.85/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 1.85/0.97  
% 1.85/0.97  ------                               Statistics
% 1.85/0.97  
% 1.85/0.97  ------ General
% 1.85/0.97  
% 1.85/0.97  abstr_ref_over_cycles:                  0
% 1.85/0.97  abstr_ref_under_cycles:                 0
% 1.85/0.97  gc_basic_clause_elim:                   0
% 1.85/0.97  forced_gc_time:                         0
% 1.85/0.97  parsing_time:                           0.01
% 1.85/0.97  unif_index_cands_time:                  0.
% 1.85/0.97  unif_index_add_time:                    0.
% 1.85/0.97  orderings_time:                         0.
% 1.85/0.97  out_proof_time:                         0.013
% 1.85/0.97  total_time:                             0.133
% 1.85/0.97  num_of_symbols:                         59
% 1.85/0.97  num_of_terms:                           2427
% 1.85/0.97  
% 1.85/0.97  ------ Preprocessing
% 1.85/0.97  
% 1.85/0.97  num_of_splits:                          1
% 1.85/0.97  num_of_split_atoms:                     1
% 1.85/0.97  num_of_reused_defs:                     0
% 1.85/0.97  num_eq_ax_congr_red:                    18
% 1.85/0.97  num_of_sem_filtered_clauses:            1
% 1.85/0.97  num_of_subtypes:                        2
% 1.85/0.97  monotx_restored_types:                  0
% 1.85/0.97  sat_num_of_epr_types:                   0
% 1.85/0.97  sat_num_of_non_cyclic_types:            0
% 1.85/0.97  sat_guarded_non_collapsed_types:        0
% 1.85/0.97  num_pure_diseq_elim:                    0
% 1.85/0.97  simp_replaced_by:                       0
% 1.85/0.97  res_preprocessed:                       127
% 1.85/0.97  prep_upred:                             0
% 1.85/0.97  prep_unflattend:                        22
% 1.85/0.97  smt_new_axioms:                         0
% 1.85/0.97  pred_elim_cands:                        8
% 1.85/0.97  pred_elim:                              7
% 1.85/0.97  pred_elim_cl:                           10
% 1.85/0.97  pred_elim_cycles:                       15
% 1.85/0.97  merged_defs:                            8
% 1.85/0.97  merged_defs_ncl:                        0
% 1.85/0.97  bin_hyper_res:                          8
% 1.85/0.97  prep_cycles:                            4
% 1.85/0.97  pred_elim_time:                         0.026
% 1.85/0.97  splitting_time:                         0.
% 1.85/0.97  sem_filter_time:                        0.
% 1.85/0.97  monotx_time:                            0.
% 1.85/0.97  subtype_inf_time:                       0.
% 1.85/0.97  
% 1.85/0.97  ------ Problem properties
% 1.85/0.97  
% 1.85/0.97  clauses:                                25
% 1.85/0.97  conjectures:                            14
% 1.85/0.97  epr:                                    11
% 1.85/0.97  horn:                                   19
% 1.85/0.97  ground:                                 15
% 1.85/0.97  unary:                                  12
% 1.85/0.97  binary:                                 3
% 1.85/0.97  lits:                                   79
% 1.85/0.97  lits_eq:                                4
% 1.85/0.97  fd_pure:                                0
% 1.85/0.97  fd_pseudo:                              0
% 1.85/0.97  fd_cond:                                0
% 1.85/0.97  fd_pseudo_cond:                         0
% 1.85/0.97  ac_symbols:                             0
% 1.85/0.97  
% 1.85/0.97  ------ Propositional Solver
% 1.85/0.97  
% 1.85/0.97  prop_solver_calls:                      26
% 1.85/0.97  prop_fast_solver_calls:                 1283
% 1.85/0.97  smt_solver_calls:                       0
% 1.85/0.97  smt_fast_solver_calls:                  0
% 1.85/0.97  prop_num_of_clauses:                    637
% 1.85/0.97  prop_preprocess_simplified:             3615
% 1.85/0.97  prop_fo_subsumed:                       35
% 1.85/0.97  prop_solver_time:                       0.
% 1.85/0.97  smt_solver_time:                        0.
% 1.85/0.97  smt_fast_solver_time:                   0.
% 1.85/0.97  prop_fast_solver_time:                  0.
% 1.85/0.97  prop_unsat_core_time:                   0.
% 1.85/0.97  
% 1.85/0.97  ------ QBF
% 1.85/0.97  
% 1.85/0.97  qbf_q_res:                              0
% 1.85/0.97  qbf_num_tautologies:                    0
% 1.85/0.97  qbf_prep_cycles:                        0
% 1.85/0.97  
% 1.85/0.97  ------ BMC1
% 1.85/0.97  
% 1.85/0.97  bmc1_current_bound:                     -1
% 1.85/0.97  bmc1_last_solved_bound:                 -1
% 1.85/0.97  bmc1_unsat_core_size:                   -1
% 1.85/0.97  bmc1_unsat_core_parents_size:           -1
% 1.85/0.97  bmc1_merge_next_fun:                    0
% 1.85/0.97  bmc1_unsat_core_clauses_time:           0.
% 1.85/0.97  
% 1.85/0.97  ------ Instantiation
% 1.85/0.97  
% 1.85/0.97  inst_num_of_clauses:                    183
% 1.85/0.97  inst_num_in_passive:                    5
% 1.85/0.97  inst_num_in_active:                     139
% 1.85/0.97  inst_num_in_unprocessed:                39
% 1.85/0.97  inst_num_of_loops:                      150
% 1.85/0.97  inst_num_of_learning_restarts:          0
% 1.85/0.97  inst_num_moves_active_passive:          9
% 1.85/0.97  inst_lit_activity:                      0
% 1.85/0.97  inst_lit_activity_moves:                0
% 1.85/0.97  inst_num_tautologies:                   0
% 1.85/0.97  inst_num_prop_implied:                  0
% 1.85/0.97  inst_num_existing_simplified:           0
% 1.85/0.97  inst_num_eq_res_simplified:             0
% 1.85/0.97  inst_num_child_elim:                    0
% 1.85/0.97  inst_num_of_dismatching_blockings:      63
% 1.85/0.97  inst_num_of_non_proper_insts:           202
% 1.85/0.97  inst_num_of_duplicates:                 0
% 1.85/0.97  inst_inst_num_from_inst_to_res:         0
% 1.85/0.97  inst_dismatching_checking_time:         0.
% 1.85/0.97  
% 1.85/0.97  ------ Resolution
% 1.85/0.97  
% 1.85/0.97  res_num_of_clauses:                     0
% 1.85/0.97  res_num_in_passive:                     0
% 1.85/0.97  res_num_in_active:                      0
% 1.85/0.97  res_num_of_loops:                       131
% 1.85/0.97  res_forward_subset_subsumed:            18
% 1.85/0.97  res_backward_subset_subsumed:           0
% 1.85/0.97  res_forward_subsumed:                   0
% 1.85/0.97  res_backward_subsumed:                  0
% 1.85/0.97  res_forward_subsumption_resolution:     3
% 1.85/0.97  res_backward_subsumption_resolution:    0
% 1.85/0.97  res_clause_to_clause_subsumption:       245
% 1.85/0.97  res_orphan_elimination:                 0
% 1.85/0.97  res_tautology_del:                      60
% 1.85/0.97  res_num_eq_res_simplified:              0
% 1.85/0.97  res_num_sel_changes:                    0
% 1.85/0.97  res_moves_from_active_to_pass:          0
% 1.85/0.97  
% 1.85/0.97  ------ Superposition
% 1.85/0.97  
% 1.85/0.97  sup_time_total:                         0.
% 1.85/0.97  sup_time_generating:                    0.
% 1.85/0.97  sup_time_sim_full:                      0.
% 1.85/0.97  sup_time_sim_immed:                     0.
% 1.85/0.97  
% 1.85/0.97  sup_num_of_clauses:                     38
% 1.85/0.97  sup_num_in_active:                      29
% 1.85/0.97  sup_num_in_passive:                     9
% 1.85/0.97  sup_num_of_loops:                       28
% 1.85/0.97  sup_fw_superposition:                   7
% 1.85/0.97  sup_bw_superposition:                   6
% 1.85/0.97  sup_immediate_simplified:               0
% 1.85/0.97  sup_given_eliminated:                   0
% 1.85/0.97  comparisons_done:                       0
% 1.85/0.97  comparisons_avoided:                    0
% 1.85/0.97  
% 1.85/0.97  ------ Simplifications
% 1.85/0.97  
% 1.85/0.97  
% 1.85/0.97  sim_fw_subset_subsumed:                 0
% 1.85/0.97  sim_bw_subset_subsumed:                 0
% 1.85/0.97  sim_fw_subsumed:                        0
% 1.85/0.97  sim_bw_subsumed:                        0
% 1.85/0.97  sim_fw_subsumption_res:                 0
% 1.85/0.97  sim_bw_subsumption_res:                 0
% 1.85/0.97  sim_tautology_del:                      2
% 1.85/0.97  sim_eq_tautology_del:                   0
% 1.85/0.97  sim_eq_res_simp:                        0
% 1.85/0.97  sim_fw_demodulated:                     0
% 1.85/0.97  sim_bw_demodulated:                     0
% 1.85/0.97  sim_light_normalised:                   3
% 1.85/0.97  sim_joinable_taut:                      0
% 1.85/0.97  sim_joinable_simp:                      0
% 1.85/0.97  sim_ac_normalised:                      0
% 1.85/0.97  sim_smt_subsumption:                    0
% 1.85/0.97  
%------------------------------------------------------------------------------
