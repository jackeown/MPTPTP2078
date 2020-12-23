%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:30 EST 2020

% Result     : Theorem 7.16s
% Output     : CNFRefutation 7.16s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 889 expanded)
%              Number of clauses        :  126 ( 230 expanded)
%              Number of leaves         :   23 ( 298 expanded)
%              Depth                    :   19
%              Number of atoms          :  889 (8282 expanded)
%              Number of equality atoms :  254 (1011 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
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
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X3) )
     => ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2))
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2))
            & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X3) )
        & m1_pre_topc(sK2,X1)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2))
                & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
                & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f54,f53,f52,f51])).

fof(f86,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f55])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
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
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f82,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f83,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f90,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f96,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f69,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f67,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f91,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f35])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1447,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1450,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1454,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3857,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1450,c_1454])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_36,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_37,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_38,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_39,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_40,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_41,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_44,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_45,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4771,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3857,c_36,c_37,c_38,c_39,c_40,c_41,c_44,c_45])).

cnf(c_4772,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4771])).

cnf(c_4780,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1447,c_4772])).

cnf(c_9,plain,
    ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3),X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(X0,X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1461,plain,
    ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3),X2) = iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4939,plain,
    ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK3) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4780,c_1461])).

cnf(c_43,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_21,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_51,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_53,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
    | m1_pre_topc(sK1,sK1) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_66,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_68,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_13,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_73,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_75,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_105,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_109,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1785,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1786,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1785])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1983,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_11,c_28])).

cnf(c_1984,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1983])).

cnf(c_2185,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2186,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2185])).

cnf(c_2188,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2186])).

cnf(c_637,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X3 != X1
    | X2 != X0 ),
    theory(equality)).

cnf(c_1918,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
    | X0 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_2295,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
    | X0 != sK1
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_1918])).

cnf(c_2296,plain,
    ( X0 != sK1
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2295])).

cnf(c_2298,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | sK1 != sK1
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2296])).

cnf(c_14,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1456,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3289,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_1456])).

cnf(c_3317,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3289])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2122,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X0))
    | r1_tarski(u1_struct_0(sK1),X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2739,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0)))
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2122])).

cnf(c_9575,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2739])).

cnf(c_9576,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9575])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2738,plain,
    ( ~ m1_pre_topc(sK1,X0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_12689,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2738])).

cnf(c_12690,plain,
    ( m1_pre_topc(sK1,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12689])).

cnf(c_13737,plain,
    ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4939,c_40,c_41,c_43,c_44,c_45,c_46,c_24,c_53,c_68,c_75,c_105,c_109,c_1786,c_1984,c_2188,c_2298,c_3317,c_9576,c_12690])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1467,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1464,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4207,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | r1_tarski(X1,k2_zfmisc_1(X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1467,c_1464])).

cnf(c_9447,plain,
    ( sK3 = X0
    | r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK3) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1450,c_4207])).

cnf(c_13743,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = sK3
    | r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13737,c_9447])).

cnf(c_23,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_644,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | r1_funct_2(X6,X7,X8,X9,X10,X11)
    | X7 != X1
    | X6 != X0
    | X8 != X2
    | X9 != X3
    | X10 != X4
    | X11 != X5 ),
    theory(equality)).

cnf(c_17,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_6571,plain,
    ( r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[status(thm)],[c_17,c_25])).

cnf(c_1455,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4) = iProver_top
    | v1_funct_2(X5,X2,X3) != iProver_top
    | v1_funct_2(X4,X0,X1) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4974,plain,
    ( r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),X2,X2) = iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1450,c_1455])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1833,plain,
    ( l1_struct_0(sK0) ),
    inference(resolution,[status(thm)],[c_10,c_33])).

cnf(c_1834,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1833])).

cnf(c_12,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2965,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2966,plain,
    ( v2_struct_0(sK0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) != iProver_top
    | l1_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2965])).

cnf(c_5431,plain,
    ( v1_funct_1(X2) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4974,c_36,c_44,c_45,c_1834,c_2966])).

cnf(c_5432,plain,
    ( r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),X2,X2) = iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5431])).

cnf(c_5433,plain,
    ( r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5432])).

cnf(c_6868,plain,
    ( ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X0,X1)
    | r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6571,c_5433])).

cnf(c_6869,plain,
    ( r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X2) ),
    inference(renaming,[status(thm)],[c_6868])).

cnf(c_7814,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(X6,X7,X8)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
    | v1_xboole_0(X8)
    | ~ v1_funct_1(X6)
    | X5 != X6
    | X1 != X8
    | X0 != X7
    | X4 != X6
    | X3 != u1_struct_0(sK0)
    | X2 != u1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_644,c_6869])).

cnf(c_8851,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | X1 != u1_struct_0(sK0)
    | X3 != u1_struct_0(sK0)
    | X0 != u1_struct_0(sK1)
    | X2 != u1_struct_0(sK1)
    | X4 != sK3
    | X5 != sK3 ),
    inference(resolution,[status(thm)],[c_7814,c_25])).

cnf(c_1850,plain,
    ( r1_funct_2(X0,X1,X2,X3,sK3,sK3)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2023,plain,
    ( r1_funct_2(X0,X1,X2,X3,sK3,sK3)
    | ~ v1_funct_2(sK3,X0,X1)
    | ~ v1_funct_2(sK3,X2,X3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1850])).

cnf(c_2139,plain,
    ( r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | ~ v1_funct_2(sK3,X0,X1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(X1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2023])).

cnf(c_2555,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2139])).

cnf(c_3807,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | X1 != u1_struct_0(sK0)
    | X3 != u1_struct_0(sK0)
    | X0 != u1_struct_0(sK1)
    | X2 != u1_struct_0(sK1)
    | X4 != sK3
    | X5 != sK3 ),
    inference(instantiation,[status(thm)],[c_644])).

cnf(c_8856,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X5)
    | X1 != u1_struct_0(sK0)
    | X3 != u1_struct_0(sK0)
    | X0 != u1_struct_0(sK1)
    | X2 != u1_struct_0(sK1)
    | X4 != sK3
    | X5 != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8851,c_35,c_27,c_26,c_25,c_1833,c_2555,c_2965,c_3807])).

cnf(c_9067,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(sK2) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK3 != sK3 ),
    inference(resolution,[status(thm)],[c_23,c_8856])).

cnf(c_9068,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(sK2) != u1_struct_0(sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_9067])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1463,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1466,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4026,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_partfun1(X1,X2,X0,X3),k2_zfmisc_1(X1,X2)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1463,c_1466])).

cnf(c_7334,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4780,c_4026])).

cnf(c_4367,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0))
    | r1_tarski(u1_struct_0(sK2),X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6064,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_4367])).

cnf(c_2373,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),X0)
    | X0 = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3065,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(X0))
    | u1_struct_0(X0) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2373])).

cnf(c_4932,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3065])).

cnf(c_3316,plain,
    ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | m1_pre_topc(X0,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3289])).

cnf(c_3318,plain,
    ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | m1_pre_topc(sK1,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3316])).

cnf(c_2297,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2295])).

cnf(c_2187,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2185])).

cnf(c_1768,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_74,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_67,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_52,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
    | m1_pre_topc(sK1,sK1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13743,c_12689,c_9575,c_9068,c_7334,c_6064,c_4932,c_3318,c_2297,c_2187,c_1983,c_1785,c_1768,c_109,c_105,c_74,c_67,c_52,c_24,c_46,c_44,c_28,c_30,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.16/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.16/1.50  
% 7.16/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.16/1.50  
% 7.16/1.50  ------  iProver source info
% 7.16/1.50  
% 7.16/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.16/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.16/1.50  git: non_committed_changes: false
% 7.16/1.50  git: last_make_outside_of_git: false
% 7.16/1.50  
% 7.16/1.50  ------ 
% 7.16/1.50  ------ Parsing...
% 7.16/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.16/1.50  
% 7.16/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.16/1.50  
% 7.16/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.16/1.50  
% 7.16/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.16/1.50  ------ Proving...
% 7.16/1.50  ------ Problem Properties 
% 7.16/1.50  
% 7.16/1.50  
% 7.16/1.50  clauses                                 33
% 7.16/1.50  conjectures                             13
% 7.16/1.50  EPR                                     13
% 7.16/1.50  Horn                                    31
% 7.16/1.50  unary                                   14
% 7.16/1.50  binary                                  4
% 7.16/1.50  lits                                    87
% 7.16/1.50  lits eq                                 4
% 7.16/1.50  fd_pure                                 0
% 7.16/1.50  fd_pseudo                               0
% 7.16/1.50  fd_cond                                 0
% 7.16/1.50  fd_pseudo_cond                          2
% 7.16/1.50  AC symbols                              0
% 7.16/1.50  
% 7.16/1.50  ------ Input Options Time Limit: Unbounded
% 7.16/1.50  
% 7.16/1.50  
% 7.16/1.50  ------ 
% 7.16/1.50  Current options:
% 7.16/1.50  ------ 
% 7.16/1.50  
% 7.16/1.50  
% 7.16/1.50  
% 7.16/1.50  
% 7.16/1.50  ------ Proving...
% 7.16/1.50  
% 7.16/1.50  
% 7.16/1.50  % SZS status Theorem for theBenchmark.p
% 7.16/1.50  
% 7.16/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.16/1.50  
% 7.16/1.50  fof(f17,conjecture,(
% 7.16/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 7.16/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.50  
% 7.16/1.50  fof(f18,negated_conjecture,(
% 7.16/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 7.16/1.50    inference(negated_conjecture,[],[f17])).
% 7.16/1.50  
% 7.16/1.50  fof(f43,plain,(
% 7.16/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.16/1.50    inference(ennf_transformation,[],[f18])).
% 7.16/1.50  
% 7.16/1.50  fof(f44,plain,(
% 7.16/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.16/1.50    inference(flattening,[],[f43])).
% 7.16/1.50  
% 7.16/1.50  fof(f54,plain,(
% 7.16/1.50    ( ! [X2,X0,X1] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 7.16/1.50    introduced(choice_axiom,[])).
% 7.16/1.50  
% 7.16/1.50  fof(f53,plain,(
% 7.16/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 7.16/1.50    introduced(choice_axiom,[])).
% 7.16/1.50  
% 7.16/1.50  fof(f52,plain,(
% 7.16/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 7.16/1.50    introduced(choice_axiom,[])).
% 7.16/1.50  
% 7.16/1.50  fof(f51,plain,(
% 7.16/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.16/1.50    introduced(choice_axiom,[])).
% 7.16/1.50  
% 7.16/1.50  fof(f55,plain,(
% 7.16/1.50    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.16/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f54,f53,f52,f51])).
% 7.16/1.50  
% 7.16/1.50  fof(f86,plain,(
% 7.16/1.50    m1_pre_topc(sK2,sK1)),
% 7.16/1.50    inference(cnf_transformation,[],[f55])).
% 7.16/1.50  
% 7.16/1.50  fof(f89,plain,(
% 7.16/1.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 7.16/1.50    inference(cnf_transformation,[],[f55])).
% 7.16/1.50  
% 7.16/1.50  fof(f13,axiom,(
% 7.16/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 7.16/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.50  
% 7.16/1.50  fof(f37,plain,(
% 7.16/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.16/1.50    inference(ennf_transformation,[],[f13])).
% 7.16/1.50  
% 7.16/1.50  fof(f38,plain,(
% 7.16/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.16/1.50    inference(flattening,[],[f37])).
% 7.16/1.50  
% 7.16/1.50  fof(f74,plain,(
% 7.16/1.50    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.16/1.50    inference(cnf_transformation,[],[f38])).
% 7.16/1.50  
% 7.16/1.50  fof(f79,plain,(
% 7.16/1.50    ~v2_struct_0(sK0)),
% 7.16/1.50    inference(cnf_transformation,[],[f55])).
% 7.16/1.50  
% 7.16/1.50  fof(f80,plain,(
% 7.16/1.50    v2_pre_topc(sK0)),
% 7.16/1.50    inference(cnf_transformation,[],[f55])).
% 7.16/1.50  
% 7.16/1.50  fof(f81,plain,(
% 7.16/1.50    l1_pre_topc(sK0)),
% 7.16/1.50    inference(cnf_transformation,[],[f55])).
% 7.16/1.50  
% 7.16/1.50  fof(f82,plain,(
% 7.16/1.50    ~v2_struct_0(sK1)),
% 7.16/1.50    inference(cnf_transformation,[],[f55])).
% 7.16/1.50  
% 7.16/1.50  fof(f83,plain,(
% 7.16/1.50    v2_pre_topc(sK1)),
% 7.16/1.50    inference(cnf_transformation,[],[f55])).
% 7.16/1.50  
% 7.16/1.50  fof(f84,plain,(
% 7.16/1.50    l1_pre_topc(sK1)),
% 7.16/1.50    inference(cnf_transformation,[],[f55])).
% 7.16/1.50  
% 7.16/1.50  fof(f87,plain,(
% 7.16/1.50    v1_funct_1(sK3)),
% 7.16/1.50    inference(cnf_transformation,[],[f55])).
% 7.16/1.50  
% 7.16/1.50  fof(f88,plain,(
% 7.16/1.50    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 7.16/1.50    inference(cnf_transformation,[],[f55])).
% 7.16/1.50  
% 7.16/1.50  fof(f5,axiom,(
% 7.16/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 7.16/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.50  
% 7.16/1.50  fof(f25,plain,(
% 7.16/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.16/1.50    inference(ennf_transformation,[],[f5])).
% 7.16/1.50  
% 7.16/1.50  fof(f26,plain,(
% 7.16/1.50    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.16/1.50    inference(flattening,[],[f25])).
% 7.16/1.50  
% 7.16/1.50  fof(f65,plain,(
% 7.16/1.50    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.16/1.50    inference(cnf_transformation,[],[f26])).
% 7.16/1.50  
% 7.16/1.50  fof(f90,plain,(
% 7.16/1.50    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 7.16/1.50    inference(cnf_transformation,[],[f55])).
% 7.16/1.50  
% 7.16/1.50  fof(f15,axiom,(
% 7.16/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 7.16/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.50  
% 7.16/1.50  fof(f40,plain,(
% 7.16/1.50    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 7.16/1.50    inference(ennf_transformation,[],[f15])).
% 7.16/1.50  
% 7.16/1.50  fof(f41,plain,(
% 7.16/1.50    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.16/1.50    inference(flattening,[],[f40])).
% 7.16/1.50  
% 7.16/1.50  fof(f50,plain,(
% 7.16/1.50    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.16/1.50    inference(nnf_transformation,[],[f41])).
% 7.16/1.50  
% 7.16/1.50  fof(f76,plain,(
% 7.16/1.50    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.16/1.50    inference(cnf_transformation,[],[f50])).
% 7.16/1.50  
% 7.16/1.50  fof(f96,plain,(
% 7.16/1.50    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 7.16/1.50    inference(equality_resolution,[],[f76])).
% 7.16/1.50  
% 7.16/1.50  fof(f11,axiom,(
% 7.16/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 7.16/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.50  
% 7.16/1.50  fof(f34,plain,(
% 7.16/1.50    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.16/1.50    inference(ennf_transformation,[],[f11])).
% 7.16/1.50  
% 7.16/1.50  fof(f49,plain,(
% 7.16/1.50    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.16/1.50    inference(nnf_transformation,[],[f34])).
% 7.16/1.50  
% 7.16/1.50  fof(f71,plain,(
% 7.16/1.50    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.16/1.50    inference(cnf_transformation,[],[f49])).
% 7.16/1.50  
% 7.16/1.50  fof(f9,axiom,(
% 7.16/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 7.16/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.50  
% 7.16/1.50  fof(f20,plain,(
% 7.16/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 7.16/1.50    inference(pure_predicate_removal,[],[f9])).
% 7.16/1.50  
% 7.16/1.50  fof(f31,plain,(
% 7.16/1.50    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.16/1.50    inference(ennf_transformation,[],[f20])).
% 7.16/1.50  
% 7.16/1.50  fof(f32,plain,(
% 7.16/1.50    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.16/1.50    inference(flattening,[],[f31])).
% 7.16/1.50  
% 7.16/1.50  fof(f69,plain,(
% 7.16/1.50    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.16/1.50    inference(cnf_transformation,[],[f32])).
% 7.16/1.50  
% 7.16/1.50  fof(f1,axiom,(
% 7.16/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.16/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.50  
% 7.16/1.50  fof(f45,plain,(
% 7.16/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.16/1.50    inference(nnf_transformation,[],[f1])).
% 7.16/1.50  
% 7.16/1.50  fof(f46,plain,(
% 7.16/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.16/1.50    inference(flattening,[],[f45])).
% 7.16/1.50  
% 7.16/1.50  fof(f56,plain,(
% 7.16/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.16/1.50    inference(cnf_transformation,[],[f46])).
% 7.16/1.50  
% 7.16/1.50  fof(f93,plain,(
% 7.16/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.16/1.50    inference(equality_resolution,[],[f56])).
% 7.16/1.50  
% 7.16/1.50  fof(f58,plain,(
% 7.16/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.16/1.50    inference(cnf_transformation,[],[f46])).
% 7.16/1.50  
% 7.16/1.50  fof(f14,axiom,(
% 7.16/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 7.16/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.50  
% 7.16/1.50  fof(f19,plain,(
% 7.16/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 7.16/1.50    inference(pure_predicate_removal,[],[f14])).
% 7.16/1.50  
% 7.16/1.50  fof(f39,plain,(
% 7.16/1.50    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.16/1.50    inference(ennf_transformation,[],[f19])).
% 7.16/1.50  
% 7.16/1.50  fof(f75,plain,(
% 7.16/1.50    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.16/1.50    inference(cnf_transformation,[],[f39])).
% 7.16/1.50  
% 7.16/1.50  fof(f7,axiom,(
% 7.16/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.16/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.50  
% 7.16/1.50  fof(f28,plain,(
% 7.16/1.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.16/1.50    inference(ennf_transformation,[],[f7])).
% 7.16/1.50  
% 7.16/1.50  fof(f67,plain,(
% 7.16/1.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.16/1.50    inference(cnf_transformation,[],[f28])).
% 7.16/1.50  
% 7.16/1.50  fof(f10,axiom,(
% 7.16/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 7.16/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.50  
% 7.16/1.50  fof(f33,plain,(
% 7.16/1.50    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.16/1.50    inference(ennf_transformation,[],[f10])).
% 7.16/1.50  
% 7.16/1.50  fof(f70,plain,(
% 7.16/1.50    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 7.16/1.50    inference(cnf_transformation,[],[f33])).
% 7.16/1.50  
% 7.16/1.50  fof(f2,axiom,(
% 7.16/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.16/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.50  
% 7.16/1.50  fof(f47,plain,(
% 7.16/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.16/1.50    inference(nnf_transformation,[],[f2])).
% 7.16/1.50  
% 7.16/1.50  fof(f59,plain,(
% 7.16/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.16/1.50    inference(cnf_transformation,[],[f47])).
% 7.16/1.50  
% 7.16/1.50  fof(f16,axiom,(
% 7.16/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.16/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.50  
% 7.16/1.50  fof(f42,plain,(
% 7.16/1.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.16/1.50    inference(ennf_transformation,[],[f16])).
% 7.16/1.50  
% 7.16/1.50  fof(f78,plain,(
% 7.16/1.50    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.16/1.50    inference(cnf_transformation,[],[f42])).
% 7.16/1.50  
% 7.16/1.50  fof(f60,plain,(
% 7.16/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.16/1.50    inference(cnf_transformation,[],[f47])).
% 7.16/1.50  
% 7.16/1.50  fof(f3,axiom,(
% 7.16/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.16/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.50  
% 7.16/1.50  fof(f21,plain,(
% 7.16/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.16/1.50    inference(ennf_transformation,[],[f3])).
% 7.16/1.50  
% 7.16/1.50  fof(f22,plain,(
% 7.16/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.16/1.50    inference(flattening,[],[f21])).
% 7.16/1.50  
% 7.16/1.50  fof(f48,plain,(
% 7.16/1.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.16/1.50    inference(nnf_transformation,[],[f22])).
% 7.16/1.50  
% 7.16/1.50  fof(f61,plain,(
% 7.16/1.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.16/1.50    inference(cnf_transformation,[],[f48])).
% 7.16/1.50  
% 7.16/1.50  fof(f91,plain,(
% 7.16/1.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 7.16/1.50    inference(cnf_transformation,[],[f55])).
% 7.16/1.50  
% 7.16/1.50  fof(f12,axiom,(
% 7.16/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 7.16/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.50  
% 7.16/1.50  fof(f35,plain,(
% 7.16/1.50    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 7.16/1.50    inference(ennf_transformation,[],[f12])).
% 7.16/1.50  
% 7.16/1.50  fof(f36,plain,(
% 7.16/1.50    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 7.16/1.50    inference(flattening,[],[f35])).
% 7.16/1.50  
% 7.16/1.50  fof(f73,plain,(
% 7.16/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 7.16/1.50    inference(cnf_transformation,[],[f36])).
% 7.16/1.50  
% 7.16/1.50  fof(f6,axiom,(
% 7.16/1.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.16/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.50  
% 7.16/1.50  fof(f27,plain,(
% 7.16/1.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.16/1.50    inference(ennf_transformation,[],[f6])).
% 7.16/1.50  
% 7.16/1.50  fof(f66,plain,(
% 7.16/1.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.16/1.50    inference(cnf_transformation,[],[f27])).
% 7.16/1.50  
% 7.16/1.50  fof(f8,axiom,(
% 7.16/1.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 7.16/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.50  
% 7.16/1.50  fof(f29,plain,(
% 7.16/1.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.16/1.50    inference(ennf_transformation,[],[f8])).
% 7.16/1.50  
% 7.16/1.50  fof(f30,plain,(
% 7.16/1.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.16/1.50    inference(flattening,[],[f29])).
% 7.16/1.50  
% 7.16/1.50  fof(f68,plain,(
% 7.16/1.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.16/1.50    inference(cnf_transformation,[],[f30])).
% 7.16/1.50  
% 7.16/1.50  fof(f4,axiom,(
% 7.16/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 7.16/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.50  
% 7.16/1.50  fof(f23,plain,(
% 7.16/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.16/1.50    inference(ennf_transformation,[],[f4])).
% 7.16/1.50  
% 7.16/1.50  fof(f24,plain,(
% 7.16/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.16/1.50    inference(flattening,[],[f23])).
% 7.16/1.50  
% 7.16/1.50  fof(f64,plain,(
% 7.16/1.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.16/1.50    inference(cnf_transformation,[],[f24])).
% 7.16/1.50  
% 7.16/1.50  cnf(c_28,negated_conjecture,
% 7.16/1.50      ( m1_pre_topc(sK2,sK1) ),
% 7.16/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_1447,plain,
% 7.16/1.50      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_25,negated_conjecture,
% 7.16/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 7.16/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_1450,plain,
% 7.16/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_18,plain,
% 7.16/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.16/1.50      | ~ m1_pre_topc(X3,X1)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.16/1.50      | ~ v2_pre_topc(X1)
% 7.16/1.50      | ~ v2_pre_topc(X2)
% 7.16/1.50      | v2_struct_0(X1)
% 7.16/1.50      | v2_struct_0(X2)
% 7.16/1.50      | ~ l1_pre_topc(X1)
% 7.16/1.50      | ~ l1_pre_topc(X2)
% 7.16/1.50      | ~ v1_funct_1(X0)
% 7.16/1.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 7.16/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_1454,plain,
% 7.16/1.50      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
% 7.16/1.50      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 7.16/1.50      | m1_pre_topc(X3,X0) != iProver_top
% 7.16/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 7.16/1.50      | v2_pre_topc(X0) != iProver_top
% 7.16/1.50      | v2_pre_topc(X1) != iProver_top
% 7.16/1.50      | v2_struct_0(X0) = iProver_top
% 7.16/1.50      | v2_struct_0(X1) = iProver_top
% 7.16/1.50      | l1_pre_topc(X0) != iProver_top
% 7.16/1.50      | l1_pre_topc(X1) != iProver_top
% 7.16/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_3857,plain,
% 7.16/1.50      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 7.16/1.50      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 7.16/1.50      | m1_pre_topc(X0,sK1) != iProver_top
% 7.16/1.50      | v2_pre_topc(sK0) != iProver_top
% 7.16/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.16/1.50      | v2_struct_0(sK0) = iProver_top
% 7.16/1.50      | v2_struct_0(sK1) = iProver_top
% 7.16/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.16/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.16/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.16/1.50      inference(superposition,[status(thm)],[c_1450,c_1454]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_35,negated_conjecture,
% 7.16/1.50      ( ~ v2_struct_0(sK0) ),
% 7.16/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_36,plain,
% 7.16/1.50      ( v2_struct_0(sK0) != iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_34,negated_conjecture,
% 7.16/1.50      ( v2_pre_topc(sK0) ),
% 7.16/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_37,plain,
% 7.16/1.50      ( v2_pre_topc(sK0) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_33,negated_conjecture,
% 7.16/1.50      ( l1_pre_topc(sK0) ),
% 7.16/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_38,plain,
% 7.16/1.50      ( l1_pre_topc(sK0) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_32,negated_conjecture,
% 7.16/1.50      ( ~ v2_struct_0(sK1) ),
% 7.16/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_39,plain,
% 7.16/1.50      ( v2_struct_0(sK1) != iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_31,negated_conjecture,
% 7.16/1.50      ( v2_pre_topc(sK1) ),
% 7.16/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_40,plain,
% 7.16/1.50      ( v2_pre_topc(sK1) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_30,negated_conjecture,
% 7.16/1.50      ( l1_pre_topc(sK1) ),
% 7.16/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_41,plain,
% 7.16/1.50      ( l1_pre_topc(sK1) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_27,negated_conjecture,
% 7.16/1.50      ( v1_funct_1(sK3) ),
% 7.16/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_44,plain,
% 7.16/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_26,negated_conjecture,
% 7.16/1.50      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 7.16/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_45,plain,
% 7.16/1.50      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_4771,plain,
% 7.16/1.50      ( m1_pre_topc(X0,sK1) != iProver_top
% 7.16/1.50      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0) ),
% 7.16/1.50      inference(global_propositional_subsumption,
% 7.16/1.50                [status(thm)],
% 7.16/1.50                [c_3857,c_36,c_37,c_38,c_39,c_40,c_41,c_44,c_45]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_4772,plain,
% 7.16/1.50      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 7.16/1.50      | m1_pre_topc(X0,sK1) != iProver_top ),
% 7.16/1.50      inference(renaming,[status(thm)],[c_4771]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_4780,plain,
% 7.16/1.50      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 7.16/1.50      inference(superposition,[status(thm)],[c_1447,c_4772]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_9,plain,
% 7.16/1.50      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3),X2)
% 7.16/1.50      | ~ v1_funct_2(X2,X0,X1)
% 7.16/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.16/1.50      | ~ r1_tarski(X0,X3)
% 7.16/1.50      | ~ v1_funct_1(X2) ),
% 7.16/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_1461,plain,
% 7.16/1.50      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3),X2) = iProver_top
% 7.16/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.16/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.16/1.50      | r1_tarski(X0,X3) != iProver_top
% 7.16/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_4939,plain,
% 7.16/1.50      ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK3) = iProver_top
% 7.16/1.50      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 7.16/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 7.16/1.50      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 7.16/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.16/1.50      inference(superposition,[status(thm)],[c_4780,c_1461]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_43,plain,
% 7.16/1.50      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_46,plain,
% 7.16/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_24,negated_conjecture,
% 7.16/1.50      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 7.16/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_21,plain,
% 7.16/1.50      ( m1_pre_topc(X0,X1)
% 7.16/1.50      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.16/1.50      | ~ v2_pre_topc(X0)
% 7.16/1.50      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.16/1.50      | ~ l1_pre_topc(X1)
% 7.16/1.50      | ~ l1_pre_topc(X0)
% 7.16/1.50      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 7.16/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_51,plain,
% 7.16/1.50      ( m1_pre_topc(X0,X1) = iProver_top
% 7.16/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 7.16/1.50      | v2_pre_topc(X0) != iProver_top
% 7.16/1.50      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 7.16/1.50      | l1_pre_topc(X1) != iProver_top
% 7.16/1.50      | l1_pre_topc(X0) != iProver_top
% 7.16/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_53,plain,
% 7.16/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
% 7.16/1.50      | m1_pre_topc(sK1,sK1) = iProver_top
% 7.16/1.50      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.16/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.16/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.16/1.50      | l1_pre_topc(sK1) != iProver_top ),
% 7.16/1.50      inference(instantiation,[status(thm)],[c_51]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_16,plain,
% 7.16/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.16/1.50      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.16/1.50      | ~ l1_pre_topc(X0)
% 7.16/1.50      | ~ l1_pre_topc(X1) ),
% 7.16/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_66,plain,
% 7.16/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.16/1.50      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 7.16/1.50      | l1_pre_topc(X1) != iProver_top
% 7.16/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_68,plain,
% 7.16/1.50      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.16/1.50      | m1_pre_topc(sK1,sK1) != iProver_top
% 7.16/1.50      | l1_pre_topc(sK1) != iProver_top ),
% 7.16/1.50      inference(instantiation,[status(thm)],[c_66]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_13,plain,
% 7.16/1.50      ( ~ v2_pre_topc(X0)
% 7.16/1.50      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.16/1.50      | ~ l1_pre_topc(X0) ),
% 7.16/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_73,plain,
% 7.16/1.50      ( v2_pre_topc(X0) != iProver_top
% 7.16/1.50      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 7.16/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_75,plain,
% 7.16/1.50      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.16/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.16/1.50      | l1_pre_topc(sK1) != iProver_top ),
% 7.16/1.50      inference(instantiation,[status(thm)],[c_73]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2,plain,
% 7.16/1.50      ( r1_tarski(X0,X0) ),
% 7.16/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_105,plain,
% 7.16/1.50      ( r1_tarski(sK1,sK1) ),
% 7.16/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_0,plain,
% 7.16/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.16/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_109,plain,
% 7.16/1.50      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 7.16/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_19,plain,
% 7.16/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.16/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.16/1.50      | ~ l1_pre_topc(X1) ),
% 7.16/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_1785,plain,
% 7.16/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
% 7.16/1.50      | ~ m1_pre_topc(sK2,sK1)
% 7.16/1.50      | ~ l1_pre_topc(sK1) ),
% 7.16/1.50      inference(instantiation,[status(thm)],[c_19]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_1786,plain,
% 7.16/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) = iProver_top
% 7.16/1.50      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.16/1.50      | l1_pre_topc(sK1) != iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_1785]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_11,plain,
% 7.16/1.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.16/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_1983,plain,
% 7.16/1.50      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK1) ),
% 7.16/1.50      inference(resolution,[status(thm)],[c_11,c_28]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_1984,plain,
% 7.16/1.50      ( l1_pre_topc(sK2) = iProver_top
% 7.16/1.50      | l1_pre_topc(sK1) != iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_1983]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2185,plain,
% 7.16/1.50      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
% 7.16/1.50      | ~ l1_pre_topc(X0)
% 7.16/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 7.16/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2186,plain,
% 7.16/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 7.16/1.50      | l1_pre_topc(X0) != iProver_top
% 7.16/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_2185]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2188,plain,
% 7.16/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
% 7.16/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.16/1.50      | l1_pre_topc(sK1) != iProver_top ),
% 7.16/1.50      inference(instantiation,[status(thm)],[c_2186]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_637,plain,
% 7.16/1.50      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X3 != X1 | X2 != X0 ),
% 7.16/1.50      theory(equality) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_1918,plain,
% 7.16/1.50      ( m1_pre_topc(X0,X1)
% 7.16/1.50      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
% 7.16/1.50      | X0 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 7.16/1.50      | X1 != sK1 ),
% 7.16/1.50      inference(instantiation,[status(thm)],[c_637]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2295,plain,
% 7.16/1.50      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
% 7.16/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
% 7.16/1.50      | X0 != sK1
% 7.16/1.50      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 7.16/1.50      inference(instantiation,[status(thm)],[c_1918]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2296,plain,
% 7.16/1.50      ( X0 != sK1
% 7.16/1.50      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 7.16/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
% 7.16/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_2295]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2298,plain,
% 7.16/1.50      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 7.16/1.50      | sK1 != sK1
% 7.16/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
% 7.16/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top ),
% 7.16/1.50      inference(instantiation,[status(thm)],[c_2296]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_14,plain,
% 7.16/1.50      ( m1_pre_topc(X0,X1)
% 7.16/1.50      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.16/1.50      | ~ l1_pre_topc(X1) ),
% 7.16/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_1456,plain,
% 7.16/1.50      ( m1_pre_topc(X0,X1) = iProver_top
% 7.16/1.50      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 7.16/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_3289,plain,
% 7.16/1.50      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.16/1.51      | m1_pre_topc(X0,sK2) = iProver_top
% 7.16/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.16/1.51      inference(superposition,[status(thm)],[c_24,c_1456]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_3317,plain,
% 7.16/1.51      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.16/1.51      | m1_pre_topc(sK1,sK2) = iProver_top
% 7.16/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_3289]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_4,plain,
% 7.16/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.16/1.51      inference(cnf_transformation,[],[f59]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_2122,plain,
% 7.16/1.51      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X0))
% 7.16/1.51      | r1_tarski(u1_struct_0(sK1),X0) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_2739,plain,
% 7.16/1.51      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0)))
% 7.16/1.51      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_2122]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_9575,plain,
% 7.16/1.51      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.51      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_2739]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_9576,plain,
% 7.16/1.51      ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.16/1.51      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 7.16/1.51      inference(predicate_to_equality,[status(thm)],[c_9575]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_22,plain,
% 7.16/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.16/1.51      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.16/1.51      | ~ l1_pre_topc(X1) ),
% 7.16/1.51      inference(cnf_transformation,[],[f78]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_2738,plain,
% 7.16/1.51      ( ~ m1_pre_topc(sK1,X0)
% 7.16/1.51      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0)))
% 7.16/1.51      | ~ l1_pre_topc(X0) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_22]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_12689,plain,
% 7.16/1.51      ( ~ m1_pre_topc(sK1,sK2)
% 7.16/1.51      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.51      | ~ l1_pre_topc(sK2) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_2738]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_12690,plain,
% 7.16/1.51      ( m1_pre_topc(sK1,sK2) != iProver_top
% 7.16/1.51      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 7.16/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.16/1.51      inference(predicate_to_equality,[status(thm)],[c_12689]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_13737,plain,
% 7.16/1.51      ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK3) = iProver_top ),
% 7.16/1.51      inference(global_propositional_subsumption,
% 7.16/1.51                [status(thm)],
% 7.16/1.51                [c_4939,c_40,c_41,c_43,c_44,c_45,c_46,c_24,c_53,c_68,
% 7.16/1.51                 c_75,c_105,c_109,c_1786,c_1984,c_2188,c_2298,c_3317,
% 7.16/1.51                 c_9576,c_12690]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_3,plain,
% 7.16/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.16/1.51      inference(cnf_transformation,[],[f60]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_1467,plain,
% 7.16/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.16/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 7.16/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_6,plain,
% 7.16/1.51      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.16/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.16/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.16/1.51      | X2 = X3 ),
% 7.16/1.51      inference(cnf_transformation,[],[f61]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_1464,plain,
% 7.16/1.51      ( X0 = X1
% 7.16/1.51      | r2_relset_1(X2,X3,X0,X1) != iProver_top
% 7.16/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.16/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 7.16/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_4207,plain,
% 7.16/1.51      ( X0 = X1
% 7.16/1.51      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 7.16/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.16/1.51      | r1_tarski(X1,k2_zfmisc_1(X2,X3)) != iProver_top ),
% 7.16/1.51      inference(superposition,[status(thm)],[c_1467,c_1464]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_9447,plain,
% 7.16/1.51      ( sK3 = X0
% 7.16/1.51      | r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK3) != iProver_top
% 7.16/1.51      | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top ),
% 7.16/1.51      inference(superposition,[status(thm)],[c_1450,c_4207]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_13743,plain,
% 7.16/1.51      ( k2_tmap_1(sK1,sK0,sK3,sK2) = sK3
% 7.16/1.51      | r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top ),
% 7.16/1.51      inference(superposition,[status(thm)],[c_13737,c_9447]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_23,negated_conjecture,
% 7.16/1.51      ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
% 7.16/1.51      inference(cnf_transformation,[],[f91]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_644,plain,
% 7.16/1.51      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 7.16/1.51      | r1_funct_2(X6,X7,X8,X9,X10,X11)
% 7.16/1.51      | X7 != X1
% 7.16/1.51      | X6 != X0
% 7.16/1.51      | X8 != X2
% 7.16/1.51      | X9 != X3
% 7.16/1.51      | X10 != X4
% 7.16/1.51      | X11 != X5 ),
% 7.16/1.51      theory(equality) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_17,plain,
% 7.16/1.51      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 7.16/1.51      | ~ v1_funct_2(X5,X2,X3)
% 7.16/1.51      | ~ v1_funct_2(X4,X0,X1)
% 7.16/1.51      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.16/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.16/1.51      | v1_xboole_0(X1)
% 7.16/1.51      | v1_xboole_0(X3)
% 7.16/1.51      | ~ v1_funct_1(X5)
% 7.16/1.51      | ~ v1_funct_1(X4) ),
% 7.16/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_6571,plain,
% 7.16/1.51      ( r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),X2,X2)
% 7.16/1.51      | ~ v1_funct_2(X2,X0,X1)
% 7.16/1.51      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 7.16/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.16/1.51      | v1_xboole_0(X1)
% 7.16/1.51      | v1_xboole_0(u1_struct_0(sK0))
% 7.16/1.51      | ~ v1_funct_1(X2)
% 7.16/1.51      | ~ v1_funct_1(sK3) ),
% 7.16/1.51      inference(resolution,[status(thm)],[c_17,c_25]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_1455,plain,
% 7.16/1.51      ( r1_funct_2(X0,X1,X2,X3,X4,X4) = iProver_top
% 7.16/1.51      | v1_funct_2(X5,X2,X3) != iProver_top
% 7.16/1.51      | v1_funct_2(X4,X0,X1) != iProver_top
% 7.16/1.51      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.16/1.51      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.16/1.51      | v1_xboole_0(X1) = iProver_top
% 7.16/1.51      | v1_xboole_0(X3) = iProver_top
% 7.16/1.51      | v1_funct_1(X5) != iProver_top
% 7.16/1.51      | v1_funct_1(X4) != iProver_top ),
% 7.16/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_4974,plain,
% 7.16/1.51      ( r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),X2,X2) = iProver_top
% 7.16/1.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.16/1.51      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 7.16/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.16/1.51      | v1_xboole_0(X1) = iProver_top
% 7.16/1.51      | v1_xboole_0(u1_struct_0(sK0)) = iProver_top
% 7.16/1.51      | v1_funct_1(X2) != iProver_top
% 7.16/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.16/1.51      inference(superposition,[status(thm)],[c_1450,c_1455]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_10,plain,
% 7.16/1.51      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.16/1.51      inference(cnf_transformation,[],[f66]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_1833,plain,
% 7.16/1.51      ( l1_struct_0(sK0) ),
% 7.16/1.51      inference(resolution,[status(thm)],[c_10,c_33]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_1834,plain,
% 7.16/1.51      ( l1_struct_0(sK0) = iProver_top ),
% 7.16/1.51      inference(predicate_to_equality,[status(thm)],[c_1833]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_12,plain,
% 7.16/1.51      ( v2_struct_0(X0)
% 7.16/1.51      | ~ v1_xboole_0(u1_struct_0(X0))
% 7.16/1.51      | ~ l1_struct_0(X0) ),
% 7.16/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_2965,plain,
% 7.16/1.51      ( v2_struct_0(sK0)
% 7.16/1.51      | ~ v1_xboole_0(u1_struct_0(sK0))
% 7.16/1.51      | ~ l1_struct_0(sK0) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_12]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_2966,plain,
% 7.16/1.51      ( v2_struct_0(sK0) = iProver_top
% 7.16/1.51      | v1_xboole_0(u1_struct_0(sK0)) != iProver_top
% 7.16/1.51      | l1_struct_0(sK0) != iProver_top ),
% 7.16/1.51      inference(predicate_to_equality,[status(thm)],[c_2965]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_5431,plain,
% 7.16/1.51      ( v1_funct_1(X2) != iProver_top
% 7.16/1.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.16/1.51      | r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),X2,X2) = iProver_top
% 7.16/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.16/1.51      | v1_xboole_0(X1) = iProver_top ),
% 7.16/1.51      inference(global_propositional_subsumption,
% 7.16/1.51                [status(thm)],
% 7.16/1.51                [c_4974,c_36,c_44,c_45,c_1834,c_2966]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_5432,plain,
% 7.16/1.51      ( r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),X2,X2) = iProver_top
% 7.16/1.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.16/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.16/1.51      | v1_xboole_0(X1) = iProver_top
% 7.16/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.16/1.51      inference(renaming,[status(thm)],[c_5431]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_5433,plain,
% 7.16/1.51      ( r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),X2,X2)
% 7.16/1.51      | ~ v1_funct_2(X2,X0,X1)
% 7.16/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.16/1.51      | v1_xboole_0(X1)
% 7.16/1.51      | ~ v1_funct_1(X2) ),
% 7.16/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_5432]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_6868,plain,
% 7.16/1.51      ( ~ v1_funct_1(X2)
% 7.16/1.51      | ~ v1_funct_2(X2,X0,X1)
% 7.16/1.51      | r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),X2,X2)
% 7.16/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.16/1.51      | v1_xboole_0(X1) ),
% 7.16/1.51      inference(global_propositional_subsumption,
% 7.16/1.51                [status(thm)],
% 7.16/1.51                [c_6571,c_5433]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_6869,plain,
% 7.16/1.51      ( r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),X2,X2)
% 7.16/1.51      | ~ v1_funct_2(X2,X0,X1)
% 7.16/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.16/1.51      | v1_xboole_0(X1)
% 7.16/1.51      | ~ v1_funct_1(X2) ),
% 7.16/1.51      inference(renaming,[status(thm)],[c_6868]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_7814,plain,
% 7.16/1.51      ( r1_funct_2(X0,X1,X2,X3,X4,X5)
% 7.16/1.51      | ~ v1_funct_2(X6,X7,X8)
% 7.16/1.51      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
% 7.16/1.51      | v1_xboole_0(X8)
% 7.16/1.51      | ~ v1_funct_1(X6)
% 7.16/1.51      | X5 != X6
% 7.16/1.51      | X1 != X8
% 7.16/1.51      | X0 != X7
% 7.16/1.51      | X4 != X6
% 7.16/1.51      | X3 != u1_struct_0(sK0)
% 7.16/1.51      | X2 != u1_struct_0(sK1) ),
% 7.16/1.51      inference(resolution,[status(thm)],[c_644,c_6869]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_8851,plain,
% 7.16/1.51      ( r1_funct_2(X0,X1,X2,X3,X4,X5)
% 7.16/1.51      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 7.16/1.51      | v1_xboole_0(u1_struct_0(sK0))
% 7.16/1.51      | ~ v1_funct_1(sK3)
% 7.16/1.51      | X1 != u1_struct_0(sK0)
% 7.16/1.51      | X3 != u1_struct_0(sK0)
% 7.16/1.51      | X0 != u1_struct_0(sK1)
% 7.16/1.51      | X2 != u1_struct_0(sK1)
% 7.16/1.51      | X4 != sK3
% 7.16/1.51      | X5 != sK3 ),
% 7.16/1.51      inference(resolution,[status(thm)],[c_7814,c_25]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_1850,plain,
% 7.16/1.51      ( r1_funct_2(X0,X1,X2,X3,sK3,sK3)
% 7.16/1.51      | ~ v1_funct_2(X4,X2,X3)
% 7.16/1.51      | ~ v1_funct_2(sK3,X0,X1)
% 7.16/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.16/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.16/1.51      | v1_xboole_0(X1)
% 7.16/1.51      | v1_xboole_0(X3)
% 7.16/1.51      | ~ v1_funct_1(X4)
% 7.16/1.51      | ~ v1_funct_1(sK3) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_17]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_2023,plain,
% 7.16/1.51      ( r1_funct_2(X0,X1,X2,X3,sK3,sK3)
% 7.16/1.51      | ~ v1_funct_2(sK3,X0,X1)
% 7.16/1.51      | ~ v1_funct_2(sK3,X2,X3)
% 7.16/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.16/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.16/1.51      | v1_xboole_0(X1)
% 7.16/1.51      | v1_xboole_0(X3)
% 7.16/1.51      | ~ v1_funct_1(sK3) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_1850]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_2139,plain,
% 7.16/1.51      ( r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
% 7.16/1.51      | ~ v1_funct_2(sK3,X0,X1)
% 7.16/1.51      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 7.16/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.16/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.16/1.51      | v1_xboole_0(X1)
% 7.16/1.51      | v1_xboole_0(u1_struct_0(sK0))
% 7.16/1.51      | ~ v1_funct_1(sK3) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_2023]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_2555,plain,
% 7.16/1.51      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
% 7.16/1.51      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 7.16/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.16/1.51      | v1_xboole_0(u1_struct_0(sK0))
% 7.16/1.51      | ~ v1_funct_1(sK3) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_2139]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_3807,plain,
% 7.16/1.51      ( r1_funct_2(X0,X1,X2,X3,X4,X5)
% 7.16/1.51      | ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
% 7.16/1.51      | X1 != u1_struct_0(sK0)
% 7.16/1.51      | X3 != u1_struct_0(sK0)
% 7.16/1.51      | X0 != u1_struct_0(sK1)
% 7.16/1.51      | X2 != u1_struct_0(sK1)
% 7.16/1.51      | X4 != sK3
% 7.16/1.51      | X5 != sK3 ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_644]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_8856,plain,
% 7.16/1.51      ( r1_funct_2(X0,X1,X2,X3,X4,X5)
% 7.16/1.51      | X1 != u1_struct_0(sK0)
% 7.16/1.51      | X3 != u1_struct_0(sK0)
% 7.16/1.51      | X0 != u1_struct_0(sK1)
% 7.16/1.51      | X2 != u1_struct_0(sK1)
% 7.16/1.51      | X4 != sK3
% 7.16/1.51      | X5 != sK3 ),
% 7.16/1.51      inference(global_propositional_subsumption,
% 7.16/1.51                [status(thm)],
% 7.16/1.51                [c_8851,c_35,c_27,c_26,c_25,c_1833,c_2555,c_2965,c_3807]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_9067,plain,
% 7.16/1.51      ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 7.16/1.51      | u1_struct_0(sK2) != u1_struct_0(sK1)
% 7.16/1.51      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 7.16/1.51      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 7.16/1.51      | sK3 != sK3 ),
% 7.16/1.51      inference(resolution,[status(thm)],[c_23,c_8856]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_9068,plain,
% 7.16/1.51      ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 7.16/1.51      | u1_struct_0(sK2) != u1_struct_0(sK1) ),
% 7.16/1.51      inference(equality_resolution_simp,[status(thm)],[c_9067]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_7,plain,
% 7.16/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.16/1.51      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.16/1.51      | ~ v1_funct_1(X0) ),
% 7.16/1.51      inference(cnf_transformation,[],[f64]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_1463,plain,
% 7.16/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.16/1.51      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.16/1.51      | v1_funct_1(X0) != iProver_top ),
% 7.16/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_1466,plain,
% 7.16/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.16/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.16/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_4026,plain,
% 7.16/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.16/1.51      | r1_tarski(k2_partfun1(X1,X2,X0,X3),k2_zfmisc_1(X1,X2)) = iProver_top
% 7.16/1.51      | v1_funct_1(X0) != iProver_top ),
% 7.16/1.51      inference(superposition,[status(thm)],[c_1463,c_1466]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_7334,plain,
% 7.16/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 7.16/1.51      | r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top
% 7.16/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.16/1.51      inference(superposition,[status(thm)],[c_4780,c_4026]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_4367,plain,
% 7.16/1.51      ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0))
% 7.16/1.51      | r1_tarski(u1_struct_0(sK2),X0) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_6064,plain,
% 7.16/1.51      ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.16/1.51      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_4367]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_2373,plain,
% 7.16/1.51      ( ~ r1_tarski(X0,u1_struct_0(sK1))
% 7.16/1.51      | ~ r1_tarski(u1_struct_0(sK1),X0)
% 7.16/1.51      | X0 = u1_struct_0(sK1) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_0]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_3065,plain,
% 7.16/1.51      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK1))
% 7.16/1.51      | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(X0))
% 7.16/1.51      | u1_struct_0(X0) = u1_struct_0(sK1) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_2373]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_4932,plain,
% 7.16/1.51      ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
% 7.16/1.51      | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
% 7.16/1.51      | u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_3065]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_3316,plain,
% 7.16/1.51      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.16/1.51      | m1_pre_topc(X0,sK2)
% 7.16/1.51      | ~ l1_pre_topc(sK2) ),
% 7.16/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_3289]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_3318,plain,
% 7.16/1.51      ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.16/1.51      | m1_pre_topc(sK1,sK2)
% 7.16/1.51      | ~ l1_pre_topc(sK2) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_3316]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_2297,plain,
% 7.16/1.51      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
% 7.16/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
% 7.16/1.51      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 7.16/1.51      | sK1 != sK1 ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_2295]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_2187,plain,
% 7.16/1.51      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
% 7.16/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.16/1.51      | ~ l1_pre_topc(sK1) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_2185]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_1768,plain,
% 7.16/1.51      ( ~ m1_pre_topc(sK2,sK1)
% 7.16/1.51      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.16/1.51      | ~ l1_pre_topc(sK1) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_22]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_74,plain,
% 7.16/1.51      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.16/1.51      | ~ v2_pre_topc(sK1)
% 7.16/1.51      | ~ l1_pre_topc(sK1) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_13]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_67,plain,
% 7.16/1.51      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.16/1.51      | ~ m1_pre_topc(sK1,sK1)
% 7.16/1.51      | ~ l1_pre_topc(sK1) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_16]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(c_52,plain,
% 7.16/1.51      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
% 7.16/1.51      | m1_pre_topc(sK1,sK1)
% 7.16/1.51      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.16/1.51      | ~ v2_pre_topc(sK1)
% 7.16/1.51      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.16/1.51      | ~ l1_pre_topc(sK1) ),
% 7.16/1.51      inference(instantiation,[status(thm)],[c_21]) ).
% 7.16/1.51  
% 7.16/1.51  cnf(contradiction,plain,
% 7.16/1.51      ( $false ),
% 7.16/1.51      inference(minisat,
% 7.16/1.51                [status(thm)],
% 7.16/1.51                [c_13743,c_12689,c_9575,c_9068,c_7334,c_6064,c_4932,
% 7.16/1.51                 c_3318,c_2297,c_2187,c_1983,c_1785,c_1768,c_109,c_105,
% 7.16/1.51                 c_74,c_67,c_52,c_24,c_46,c_44,c_28,c_30,c_31]) ).
% 7.16/1.51  
% 7.16/1.51  
% 7.16/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.16/1.51  
% 7.16/1.51  ------                               Statistics
% 7.16/1.51  
% 7.16/1.51  ------ Selected
% 7.16/1.51  
% 7.16/1.51  total_time:                             0.521
% 7.16/1.51  
%------------------------------------------------------------------------------
