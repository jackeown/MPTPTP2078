%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:23 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  248 (1495 expanded)
%              Number of clauses        :  148 ( 408 expanded)
%              Number of leaves         :   24 ( 441 expanded)
%              Depth                    :   29
%              Number of atoms          : 1013 (11948 expanded)
%              Number of equality atoms :  348 (1553 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f62,plain,(
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

fof(f61,plain,(
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

fof(f60,plain,(
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

fof(f59,plain,
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

fof(f63,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f51,f62,f61,f60,f59])).

fof(f97,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f103,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f49])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f94,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f95,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f100,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f63])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f98,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f99,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f63])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f77,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f92,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f101,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f63])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f16,axiom,(
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

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f108,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f38,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f80,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f78,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f104,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f91,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f93,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f40])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 != X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f106,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(equality_resolution,[],[f82])).

fof(f102,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f63])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1967,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1980,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1970,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) = iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3425,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1980,c_1970])).

cnf(c_6554,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1967,c_3425])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_43,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_44,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_46,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2274,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | m1_pre_topc(sK2,X0)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2455,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2274])).

cnf(c_2456,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2455])).

cnf(c_2819,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2820,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2819])).

cnf(c_6598,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6554,c_43,c_44,c_46,c_2456,c_2820])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1969,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_11,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_513,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_7,c_11])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_513,c_11,c_7,c_6])).

cnf(c_518,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_517])).

cnf(c_574,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_8,c_518])).

cnf(c_578,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_574,c_11,c_8,c_7,c_6])).

cnf(c_579,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_578])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_712,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_579,c_30])).

cnf(c_713,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | k1_relat_1(sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_712])).

cnf(c_1957,plain,
    ( k1_relat_1(sK3) = X0
    | v1_funct_2(sK3,X0,X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_2604,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1969,c_1957])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_48,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2710,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2604,c_48])).

cnf(c_13,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_15,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_495,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_13,c_15])).

cnf(c_1958,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_2836,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3)
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2710,c_1958])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_39,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_41,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3162,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2836,c_39,c_41])).

cnf(c_27,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3170,plain,
    ( g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(demodulation,[status(thm)],[c_3162,c_27])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1973,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4093,plain,
    ( m1_pre_topc(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)),X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3170,c_1973])).

cnf(c_22,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_16,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_213,plain,
    ( ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_16])).

cnf(c_214,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(renaming,[status(thm)],[c_213])).

cnf(c_1959,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_214])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1975,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2102,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1959,c_1975])).

cnf(c_4892,plain,
    ( m1_pre_topc(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_pre_topc(sK1,X0) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3162,c_2102])).

cnf(c_7164,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_pre_topc(sK1,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4892,c_43,c_44])).

cnf(c_7165,plain,
    ( m1_pre_topc(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_pre_topc(sK1,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7164])).

cnf(c_7174,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK1,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4093,c_7165])).

cnf(c_7195,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6598,c_7174])).

cnf(c_2974,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1967,c_1975])).

cnf(c_7733,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7195,c_44,c_2974])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1972,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1978,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3670,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1972,c_1978])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1971,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4087,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1967,c_1971])).

cnf(c_4310,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4087,c_43,c_44])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1981,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4320,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK2)
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4310,c_1981])).

cnf(c_5004,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK2)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3670,c_4320])).

cnf(c_6403,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5004,c_44,c_2974])).

cnf(c_6404,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK2)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6403])).

cnf(c_6413,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_pre_topc(sK1,sK2) != iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1967,c_6404])).

cnf(c_6414,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | m1_pre_topc(sK1,sK2) != iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6413,c_3162])).

cnf(c_58,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_60,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
    | m1_pre_topc(sK1,sK1) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_76,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_78,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_115,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_119,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2249,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2250,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2249])).

cnf(c_2277,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2278,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2277])).

cnf(c_2280,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2278])).

cnf(c_1231,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2309,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
    | X0 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1231])).

cnf(c_2627,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
    | X0 != sK1
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_2309])).

cnf(c_2628,plain,
    ( X0 != sK1
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2627])).

cnf(c_2630,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | sK1 != sK1
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2628])).

cnf(c_6833,plain,
    ( m1_pre_topc(sK1,sK2) != iProver_top
    | u1_struct_0(sK2) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6414,c_43,c_44,c_46,c_27,c_60,c_78,c_115,c_119,c_2250,c_2280,c_2630])).

cnf(c_6834,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | m1_pre_topc(sK1,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6833])).

cnf(c_7747,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_7733,c_6834])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f83])).

cnf(c_730,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_731,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2) ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_1956,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2)
    | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_2727,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1969,c_1956])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_766,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_30])).

cnf(c_767,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_766])).

cnf(c_1955,plain,
    ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_767])).

cnf(c_2498,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1969,c_1955])).

cnf(c_2728,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2727,c_2498])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_40,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_42,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2797,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2728,c_39,c_40,c_41,c_42,c_43,c_44,c_48])).

cnf(c_2805,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_1967,c_2797])).

cnf(c_17,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_26,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_608,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X0,X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK1,sK0,sK3,sK2) != X0
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK0) != X2
    | u1_struct_0(sK0) != X4
    | u1_struct_0(sK1) != X3
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_609,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_778,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_609])).

cnf(c_1954,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_778])).

cnf(c_2807,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2805,c_1954])).

cnf(c_3166,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3162,c_2807])).

cnf(c_3056,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_3057,plain,
    ( v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3056])).

cnf(c_5642,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3166,c_39,c_41,c_3057])).

cnf(c_5643,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5642])).

cnf(c_8006,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) != sK3
    | v1_funct_2(k7_relat_1(sK3,k1_relat_1(sK3)),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_relat_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7747,c_5643])).

cnf(c_1976,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2959,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1969,c_1976])).

cnf(c_5,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1977,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3558,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1980,c_1977])).

cnf(c_4206,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_2959,c_3558])).

cnf(c_8058,plain,
    ( sK3 != sK3
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8006,c_4206])).

cnf(c_8059,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8058])).

cnf(c_1968,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3169,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3162,c_1968])).

cnf(c_3168,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3162,c_1969])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8059,c_3169,c_3168])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.37/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.00  
% 3.37/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.37/1.00  
% 3.37/1.00  ------  iProver source info
% 3.37/1.00  
% 3.37/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.37/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.37/1.00  git: non_committed_changes: false
% 3.37/1.00  git: last_make_outside_of_git: false
% 3.37/1.00  
% 3.37/1.00  ------ 
% 3.37/1.00  
% 3.37/1.00  ------ Input Options
% 3.37/1.00  
% 3.37/1.00  --out_options                           all
% 3.37/1.00  --tptp_safe_out                         true
% 3.37/1.00  --problem_path                          ""
% 3.37/1.00  --include_path                          ""
% 3.37/1.00  --clausifier                            res/vclausify_rel
% 3.37/1.00  --clausifier_options                    --mode clausify
% 3.37/1.00  --stdin                                 false
% 3.37/1.00  --stats_out                             all
% 3.37/1.00  
% 3.37/1.00  ------ General Options
% 3.37/1.00  
% 3.37/1.00  --fof                                   false
% 3.37/1.00  --time_out_real                         305.
% 3.37/1.00  --time_out_virtual                      -1.
% 3.37/1.00  --symbol_type_check                     false
% 3.37/1.00  --clausify_out                          false
% 3.37/1.00  --sig_cnt_out                           false
% 3.37/1.00  --trig_cnt_out                          false
% 3.37/1.00  --trig_cnt_out_tolerance                1.
% 3.37/1.00  --trig_cnt_out_sk_spl                   false
% 3.37/1.00  --abstr_cl_out                          false
% 3.37/1.00  
% 3.37/1.00  ------ Global Options
% 3.37/1.00  
% 3.37/1.00  --schedule                              default
% 3.37/1.00  --add_important_lit                     false
% 3.37/1.00  --prop_solver_per_cl                    1000
% 3.37/1.00  --min_unsat_core                        false
% 3.37/1.00  --soft_assumptions                      false
% 3.37/1.00  --soft_lemma_size                       3
% 3.37/1.00  --prop_impl_unit_size                   0
% 3.37/1.00  --prop_impl_unit                        []
% 3.37/1.00  --share_sel_clauses                     true
% 3.37/1.00  --reset_solvers                         false
% 3.37/1.00  --bc_imp_inh                            [conj_cone]
% 3.37/1.00  --conj_cone_tolerance                   3.
% 3.37/1.00  --extra_neg_conj                        none
% 3.37/1.00  --large_theory_mode                     true
% 3.37/1.00  --prolific_symb_bound                   200
% 3.37/1.00  --lt_threshold                          2000
% 3.37/1.00  --clause_weak_htbl                      true
% 3.37/1.00  --gc_record_bc_elim                     false
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing Options
% 3.37/1.00  
% 3.37/1.00  --preprocessing_flag                    true
% 3.37/1.00  --time_out_prep_mult                    0.1
% 3.37/1.00  --splitting_mode                        input
% 3.37/1.00  --splitting_grd                         true
% 3.37/1.00  --splitting_cvd                         false
% 3.37/1.00  --splitting_cvd_svl                     false
% 3.37/1.00  --splitting_nvd                         32
% 3.37/1.00  --sub_typing                            true
% 3.37/1.00  --prep_gs_sim                           true
% 3.37/1.00  --prep_unflatten                        true
% 3.37/1.00  --prep_res_sim                          true
% 3.37/1.00  --prep_upred                            true
% 3.37/1.00  --prep_sem_filter                       exhaustive
% 3.37/1.00  --prep_sem_filter_out                   false
% 3.37/1.00  --pred_elim                             true
% 3.37/1.00  --res_sim_input                         true
% 3.37/1.00  --eq_ax_congr_red                       true
% 3.37/1.00  --pure_diseq_elim                       true
% 3.37/1.00  --brand_transform                       false
% 3.37/1.00  --non_eq_to_eq                          false
% 3.37/1.00  --prep_def_merge                        true
% 3.37/1.00  --prep_def_merge_prop_impl              false
% 3.37/1.00  --prep_def_merge_mbd                    true
% 3.37/1.00  --prep_def_merge_tr_red                 false
% 3.37/1.00  --prep_def_merge_tr_cl                  false
% 3.37/1.00  --smt_preprocessing                     true
% 3.37/1.00  --smt_ac_axioms                         fast
% 3.37/1.00  --preprocessed_out                      false
% 3.37/1.00  --preprocessed_stats                    false
% 3.37/1.00  
% 3.37/1.00  ------ Abstraction refinement Options
% 3.37/1.00  
% 3.37/1.00  --abstr_ref                             []
% 3.37/1.00  --abstr_ref_prep                        false
% 3.37/1.00  --abstr_ref_until_sat                   false
% 3.37/1.00  --abstr_ref_sig_restrict                funpre
% 3.37/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/1.00  --abstr_ref_under                       []
% 3.37/1.00  
% 3.37/1.00  ------ SAT Options
% 3.37/1.00  
% 3.37/1.00  --sat_mode                              false
% 3.37/1.00  --sat_fm_restart_options                ""
% 3.37/1.00  --sat_gr_def                            false
% 3.37/1.00  --sat_epr_types                         true
% 3.37/1.00  --sat_non_cyclic_types                  false
% 3.37/1.00  --sat_finite_models                     false
% 3.37/1.00  --sat_fm_lemmas                         false
% 3.37/1.00  --sat_fm_prep                           false
% 3.37/1.00  --sat_fm_uc_incr                        true
% 3.37/1.00  --sat_out_model                         small
% 3.37/1.00  --sat_out_clauses                       false
% 3.37/1.00  
% 3.37/1.00  ------ QBF Options
% 3.37/1.00  
% 3.37/1.00  --qbf_mode                              false
% 3.37/1.00  --qbf_elim_univ                         false
% 3.37/1.00  --qbf_dom_inst                          none
% 3.37/1.00  --qbf_dom_pre_inst                      false
% 3.37/1.00  --qbf_sk_in                             false
% 3.37/1.00  --qbf_pred_elim                         true
% 3.37/1.00  --qbf_split                             512
% 3.37/1.00  
% 3.37/1.00  ------ BMC1 Options
% 3.37/1.00  
% 3.37/1.00  --bmc1_incremental                      false
% 3.37/1.00  --bmc1_axioms                           reachable_all
% 3.37/1.00  --bmc1_min_bound                        0
% 3.37/1.00  --bmc1_max_bound                        -1
% 3.37/1.00  --bmc1_max_bound_default                -1
% 3.37/1.00  --bmc1_symbol_reachability              true
% 3.37/1.00  --bmc1_property_lemmas                  false
% 3.37/1.00  --bmc1_k_induction                      false
% 3.37/1.00  --bmc1_non_equiv_states                 false
% 3.37/1.00  --bmc1_deadlock                         false
% 3.37/1.00  --bmc1_ucm                              false
% 3.37/1.00  --bmc1_add_unsat_core                   none
% 3.37/1.00  --bmc1_unsat_core_children              false
% 3.37/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/1.00  --bmc1_out_stat                         full
% 3.37/1.00  --bmc1_ground_init                      false
% 3.37/1.00  --bmc1_pre_inst_next_state              false
% 3.37/1.00  --bmc1_pre_inst_state                   false
% 3.37/1.00  --bmc1_pre_inst_reach_state             false
% 3.37/1.00  --bmc1_out_unsat_core                   false
% 3.37/1.00  --bmc1_aig_witness_out                  false
% 3.37/1.00  --bmc1_verbose                          false
% 3.37/1.00  --bmc1_dump_clauses_tptp                false
% 3.37/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.37/1.00  --bmc1_dump_file                        -
% 3.37/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.37/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.37/1.00  --bmc1_ucm_extend_mode                  1
% 3.37/1.00  --bmc1_ucm_init_mode                    2
% 3.37/1.00  --bmc1_ucm_cone_mode                    none
% 3.37/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.37/1.00  --bmc1_ucm_relax_model                  4
% 3.37/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.37/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/1.00  --bmc1_ucm_layered_model                none
% 3.37/1.00  --bmc1_ucm_max_lemma_size               10
% 3.37/1.00  
% 3.37/1.00  ------ AIG Options
% 3.37/1.00  
% 3.37/1.00  --aig_mode                              false
% 3.37/1.00  
% 3.37/1.00  ------ Instantiation Options
% 3.37/1.00  
% 3.37/1.00  --instantiation_flag                    true
% 3.37/1.00  --inst_sos_flag                         false
% 3.37/1.00  --inst_sos_phase                        true
% 3.37/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/1.00  --inst_lit_sel_side                     num_symb
% 3.37/1.00  --inst_solver_per_active                1400
% 3.37/1.00  --inst_solver_calls_frac                1.
% 3.37/1.00  --inst_passive_queue_type               priority_queues
% 3.37/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/1.00  --inst_passive_queues_freq              [25;2]
% 3.37/1.00  --inst_dismatching                      true
% 3.37/1.00  --inst_eager_unprocessed_to_passive     true
% 3.37/1.00  --inst_prop_sim_given                   true
% 3.37/1.00  --inst_prop_sim_new                     false
% 3.37/1.00  --inst_subs_new                         false
% 3.37/1.00  --inst_eq_res_simp                      false
% 3.37/1.00  --inst_subs_given                       false
% 3.37/1.00  --inst_orphan_elimination               true
% 3.37/1.00  --inst_learning_loop_flag               true
% 3.37/1.00  --inst_learning_start                   3000
% 3.37/1.00  --inst_learning_factor                  2
% 3.37/1.00  --inst_start_prop_sim_after_learn       3
% 3.37/1.00  --inst_sel_renew                        solver
% 3.37/1.00  --inst_lit_activity_flag                true
% 3.37/1.00  --inst_restr_to_given                   false
% 3.37/1.00  --inst_activity_threshold               500
% 3.37/1.00  --inst_out_proof                        true
% 3.37/1.00  
% 3.37/1.00  ------ Resolution Options
% 3.37/1.00  
% 3.37/1.00  --resolution_flag                       true
% 3.37/1.00  --res_lit_sel                           adaptive
% 3.37/1.00  --res_lit_sel_side                      none
% 3.37/1.00  --res_ordering                          kbo
% 3.37/1.00  --res_to_prop_solver                    active
% 3.37/1.00  --res_prop_simpl_new                    false
% 3.37/1.00  --res_prop_simpl_given                  true
% 3.37/1.00  --res_passive_queue_type                priority_queues
% 3.37/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/1.00  --res_passive_queues_freq               [15;5]
% 3.37/1.00  --res_forward_subs                      full
% 3.37/1.00  --res_backward_subs                     full
% 3.37/1.00  --res_forward_subs_resolution           true
% 3.37/1.00  --res_backward_subs_resolution          true
% 3.37/1.00  --res_orphan_elimination                true
% 3.37/1.00  --res_time_limit                        2.
% 3.37/1.00  --res_out_proof                         true
% 3.37/1.00  
% 3.37/1.00  ------ Superposition Options
% 3.37/1.00  
% 3.37/1.00  --superposition_flag                    true
% 3.37/1.00  --sup_passive_queue_type                priority_queues
% 3.37/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.37/1.00  --demod_completeness_check              fast
% 3.37/1.00  --demod_use_ground                      true
% 3.37/1.00  --sup_to_prop_solver                    passive
% 3.37/1.00  --sup_prop_simpl_new                    true
% 3.37/1.00  --sup_prop_simpl_given                  true
% 3.37/1.00  --sup_fun_splitting                     false
% 3.37/1.00  --sup_smt_interval                      50000
% 3.37/1.00  
% 3.37/1.00  ------ Superposition Simplification Setup
% 3.37/1.00  
% 3.37/1.00  --sup_indices_passive                   []
% 3.37/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/1.00  --sup_full_bw                           [BwDemod]
% 3.37/1.00  --sup_immed_triv                        [TrivRules]
% 3.37/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/1.00  --sup_immed_bw_main                     []
% 3.37/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/1.00  
% 3.37/1.00  ------ Combination Options
% 3.37/1.00  
% 3.37/1.00  --comb_res_mult                         3
% 3.37/1.00  --comb_sup_mult                         2
% 3.37/1.00  --comb_inst_mult                        10
% 3.37/1.00  
% 3.37/1.00  ------ Debug Options
% 3.37/1.00  
% 3.37/1.00  --dbg_backtrace                         false
% 3.37/1.00  --dbg_dump_prop_clauses                 false
% 3.37/1.00  --dbg_dump_prop_clauses_file            -
% 3.37/1.00  --dbg_out_stat                          false
% 3.37/1.00  ------ Parsing...
% 3.37/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/1.00  ------ Proving...
% 3.37/1.00  ------ Problem Properties 
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  clauses                                 29
% 3.37/1.00  conjectures                             11
% 3.37/1.00  EPR                                     11
% 3.37/1.00  Horn                                    27
% 3.37/1.00  unary                                   12
% 3.37/1.00  binary                                  4
% 3.37/1.00  lits                                    79
% 3.37/1.00  lits eq                                 7
% 3.37/1.00  fd_pure                                 0
% 3.37/1.00  fd_pseudo                               0
% 3.37/1.00  fd_cond                                 1
% 3.37/1.00  fd_pseudo_cond                          1
% 3.37/1.00  AC symbols                              0
% 3.37/1.00  
% 3.37/1.00  ------ Schedule dynamic 5 is on 
% 3.37/1.00  
% 3.37/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ 
% 3.37/1.00  Current options:
% 3.37/1.00  ------ 
% 3.37/1.00  
% 3.37/1.00  ------ Input Options
% 3.37/1.00  
% 3.37/1.00  --out_options                           all
% 3.37/1.00  --tptp_safe_out                         true
% 3.37/1.00  --problem_path                          ""
% 3.37/1.00  --include_path                          ""
% 3.37/1.00  --clausifier                            res/vclausify_rel
% 3.37/1.00  --clausifier_options                    --mode clausify
% 3.37/1.00  --stdin                                 false
% 3.37/1.00  --stats_out                             all
% 3.37/1.00  
% 3.37/1.00  ------ General Options
% 3.37/1.00  
% 3.37/1.00  --fof                                   false
% 3.37/1.00  --time_out_real                         305.
% 3.37/1.00  --time_out_virtual                      -1.
% 3.37/1.00  --symbol_type_check                     false
% 3.37/1.00  --clausify_out                          false
% 3.37/1.00  --sig_cnt_out                           false
% 3.37/1.00  --trig_cnt_out                          false
% 3.37/1.00  --trig_cnt_out_tolerance                1.
% 3.37/1.00  --trig_cnt_out_sk_spl                   false
% 3.37/1.00  --abstr_cl_out                          false
% 3.37/1.00  
% 3.37/1.00  ------ Global Options
% 3.37/1.00  
% 3.37/1.00  --schedule                              default
% 3.37/1.00  --add_important_lit                     false
% 3.37/1.00  --prop_solver_per_cl                    1000
% 3.37/1.00  --min_unsat_core                        false
% 3.37/1.00  --soft_assumptions                      false
% 3.37/1.00  --soft_lemma_size                       3
% 3.37/1.00  --prop_impl_unit_size                   0
% 3.37/1.00  --prop_impl_unit                        []
% 3.37/1.00  --share_sel_clauses                     true
% 3.37/1.00  --reset_solvers                         false
% 3.37/1.00  --bc_imp_inh                            [conj_cone]
% 3.37/1.00  --conj_cone_tolerance                   3.
% 3.37/1.00  --extra_neg_conj                        none
% 3.37/1.00  --large_theory_mode                     true
% 3.37/1.00  --prolific_symb_bound                   200
% 3.37/1.00  --lt_threshold                          2000
% 3.37/1.00  --clause_weak_htbl                      true
% 3.37/1.00  --gc_record_bc_elim                     false
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing Options
% 3.37/1.00  
% 3.37/1.00  --preprocessing_flag                    true
% 3.37/1.00  --time_out_prep_mult                    0.1
% 3.37/1.00  --splitting_mode                        input
% 3.37/1.00  --splitting_grd                         true
% 3.37/1.00  --splitting_cvd                         false
% 3.37/1.00  --splitting_cvd_svl                     false
% 3.37/1.00  --splitting_nvd                         32
% 3.37/1.00  --sub_typing                            true
% 3.37/1.00  --prep_gs_sim                           true
% 3.37/1.00  --prep_unflatten                        true
% 3.37/1.00  --prep_res_sim                          true
% 3.37/1.00  --prep_upred                            true
% 3.37/1.00  --prep_sem_filter                       exhaustive
% 3.37/1.00  --prep_sem_filter_out                   false
% 3.37/1.00  --pred_elim                             true
% 3.37/1.00  --res_sim_input                         true
% 3.37/1.00  --eq_ax_congr_red                       true
% 3.37/1.00  --pure_diseq_elim                       true
% 3.37/1.00  --brand_transform                       false
% 3.37/1.00  --non_eq_to_eq                          false
% 3.37/1.00  --prep_def_merge                        true
% 3.37/1.00  --prep_def_merge_prop_impl              false
% 3.37/1.00  --prep_def_merge_mbd                    true
% 3.37/1.00  --prep_def_merge_tr_red                 false
% 3.37/1.00  --prep_def_merge_tr_cl                  false
% 3.37/1.00  --smt_preprocessing                     true
% 3.37/1.00  --smt_ac_axioms                         fast
% 3.37/1.00  --preprocessed_out                      false
% 3.37/1.00  --preprocessed_stats                    false
% 3.37/1.00  
% 3.37/1.00  ------ Abstraction refinement Options
% 3.37/1.00  
% 3.37/1.00  --abstr_ref                             []
% 3.37/1.00  --abstr_ref_prep                        false
% 3.37/1.00  --abstr_ref_until_sat                   false
% 3.37/1.00  --abstr_ref_sig_restrict                funpre
% 3.37/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/1.00  --abstr_ref_under                       []
% 3.37/1.00  
% 3.37/1.00  ------ SAT Options
% 3.37/1.00  
% 3.37/1.00  --sat_mode                              false
% 3.37/1.00  --sat_fm_restart_options                ""
% 3.37/1.00  --sat_gr_def                            false
% 3.37/1.00  --sat_epr_types                         true
% 3.37/1.00  --sat_non_cyclic_types                  false
% 3.37/1.00  --sat_finite_models                     false
% 3.37/1.00  --sat_fm_lemmas                         false
% 3.37/1.00  --sat_fm_prep                           false
% 3.37/1.00  --sat_fm_uc_incr                        true
% 3.37/1.00  --sat_out_model                         small
% 3.37/1.00  --sat_out_clauses                       false
% 3.37/1.00  
% 3.37/1.00  ------ QBF Options
% 3.37/1.00  
% 3.37/1.00  --qbf_mode                              false
% 3.37/1.00  --qbf_elim_univ                         false
% 3.37/1.00  --qbf_dom_inst                          none
% 3.37/1.00  --qbf_dom_pre_inst                      false
% 3.37/1.00  --qbf_sk_in                             false
% 3.37/1.00  --qbf_pred_elim                         true
% 3.37/1.00  --qbf_split                             512
% 3.37/1.00  
% 3.37/1.00  ------ BMC1 Options
% 3.37/1.00  
% 3.37/1.00  --bmc1_incremental                      false
% 3.37/1.00  --bmc1_axioms                           reachable_all
% 3.37/1.00  --bmc1_min_bound                        0
% 3.37/1.00  --bmc1_max_bound                        -1
% 3.37/1.00  --bmc1_max_bound_default                -1
% 3.37/1.00  --bmc1_symbol_reachability              true
% 3.37/1.00  --bmc1_property_lemmas                  false
% 3.37/1.00  --bmc1_k_induction                      false
% 3.37/1.00  --bmc1_non_equiv_states                 false
% 3.37/1.00  --bmc1_deadlock                         false
% 3.37/1.00  --bmc1_ucm                              false
% 3.37/1.00  --bmc1_add_unsat_core                   none
% 3.37/1.00  --bmc1_unsat_core_children              false
% 3.37/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/1.00  --bmc1_out_stat                         full
% 3.37/1.00  --bmc1_ground_init                      false
% 3.37/1.00  --bmc1_pre_inst_next_state              false
% 3.37/1.00  --bmc1_pre_inst_state                   false
% 3.37/1.00  --bmc1_pre_inst_reach_state             false
% 3.37/1.00  --bmc1_out_unsat_core                   false
% 3.37/1.00  --bmc1_aig_witness_out                  false
% 3.37/1.00  --bmc1_verbose                          false
% 3.37/1.00  --bmc1_dump_clauses_tptp                false
% 3.37/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.37/1.00  --bmc1_dump_file                        -
% 3.37/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.37/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.37/1.00  --bmc1_ucm_extend_mode                  1
% 3.37/1.00  --bmc1_ucm_init_mode                    2
% 3.37/1.00  --bmc1_ucm_cone_mode                    none
% 3.37/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.37/1.00  --bmc1_ucm_relax_model                  4
% 3.37/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.37/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/1.00  --bmc1_ucm_layered_model                none
% 3.37/1.00  --bmc1_ucm_max_lemma_size               10
% 3.37/1.00  
% 3.37/1.00  ------ AIG Options
% 3.37/1.00  
% 3.37/1.00  --aig_mode                              false
% 3.37/1.00  
% 3.37/1.00  ------ Instantiation Options
% 3.37/1.00  
% 3.37/1.00  --instantiation_flag                    true
% 3.37/1.00  --inst_sos_flag                         false
% 3.37/1.00  --inst_sos_phase                        true
% 3.37/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/1.00  --inst_lit_sel_side                     none
% 3.37/1.00  --inst_solver_per_active                1400
% 3.37/1.00  --inst_solver_calls_frac                1.
% 3.37/1.00  --inst_passive_queue_type               priority_queues
% 3.37/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/1.00  --inst_passive_queues_freq              [25;2]
% 3.37/1.00  --inst_dismatching                      true
% 3.37/1.00  --inst_eager_unprocessed_to_passive     true
% 3.37/1.00  --inst_prop_sim_given                   true
% 3.37/1.00  --inst_prop_sim_new                     false
% 3.37/1.00  --inst_subs_new                         false
% 3.37/1.00  --inst_eq_res_simp                      false
% 3.37/1.00  --inst_subs_given                       false
% 3.37/1.00  --inst_orphan_elimination               true
% 3.37/1.00  --inst_learning_loop_flag               true
% 3.37/1.00  --inst_learning_start                   3000
% 3.37/1.00  --inst_learning_factor                  2
% 3.37/1.00  --inst_start_prop_sim_after_learn       3
% 3.37/1.00  --inst_sel_renew                        solver
% 3.37/1.00  --inst_lit_activity_flag                true
% 3.37/1.00  --inst_restr_to_given                   false
% 3.37/1.00  --inst_activity_threshold               500
% 3.37/1.00  --inst_out_proof                        true
% 3.37/1.00  
% 3.37/1.00  ------ Resolution Options
% 3.37/1.00  
% 3.37/1.00  --resolution_flag                       false
% 3.37/1.00  --res_lit_sel                           adaptive
% 3.37/1.00  --res_lit_sel_side                      none
% 3.37/1.00  --res_ordering                          kbo
% 3.37/1.00  --res_to_prop_solver                    active
% 3.37/1.00  --res_prop_simpl_new                    false
% 3.37/1.00  --res_prop_simpl_given                  true
% 3.37/1.00  --res_passive_queue_type                priority_queues
% 3.37/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/1.00  --res_passive_queues_freq               [15;5]
% 3.37/1.00  --res_forward_subs                      full
% 3.37/1.00  --res_backward_subs                     full
% 3.37/1.00  --res_forward_subs_resolution           true
% 3.37/1.00  --res_backward_subs_resolution          true
% 3.37/1.00  --res_orphan_elimination                true
% 3.37/1.00  --res_time_limit                        2.
% 3.37/1.00  --res_out_proof                         true
% 3.37/1.00  
% 3.37/1.00  ------ Superposition Options
% 3.37/1.00  
% 3.37/1.00  --superposition_flag                    true
% 3.37/1.00  --sup_passive_queue_type                priority_queues
% 3.37/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.37/1.00  --demod_completeness_check              fast
% 3.37/1.00  --demod_use_ground                      true
% 3.37/1.00  --sup_to_prop_solver                    passive
% 3.37/1.00  --sup_prop_simpl_new                    true
% 3.37/1.00  --sup_prop_simpl_given                  true
% 3.37/1.00  --sup_fun_splitting                     false
% 3.37/1.00  --sup_smt_interval                      50000
% 3.37/1.00  
% 3.37/1.00  ------ Superposition Simplification Setup
% 3.37/1.00  
% 3.37/1.00  --sup_indices_passive                   []
% 3.37/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/1.00  --sup_full_bw                           [BwDemod]
% 3.37/1.00  --sup_immed_triv                        [TrivRules]
% 3.37/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/1.00  --sup_immed_bw_main                     []
% 3.37/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/1.00  
% 3.37/1.00  ------ Combination Options
% 3.37/1.00  
% 3.37/1.00  --comb_res_mult                         3
% 3.37/1.00  --comb_sup_mult                         2
% 3.37/1.00  --comb_inst_mult                        10
% 3.37/1.00  
% 3.37/1.00  ------ Debug Options
% 3.37/1.00  
% 3.37/1.00  --dbg_backtrace                         false
% 3.37/1.00  --dbg_dump_prop_clauses                 false
% 3.37/1.00  --dbg_dump_prop_clauses_file            -
% 3.37/1.00  --dbg_out_stat                          false
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ Proving...
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  % SZS status Theorem for theBenchmark.p
% 3.37/1.00  
% 3.37/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.37/1.00  
% 3.37/1.00  fof(f19,conjecture,(
% 3.37/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f20,negated_conjecture,(
% 3.37/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 3.37/1.00    inference(negated_conjecture,[],[f19])).
% 3.37/1.00  
% 3.37/1.00  fof(f50,plain,(
% 3.37/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.37/1.00    inference(ennf_transformation,[],[f20])).
% 3.37/1.00  
% 3.37/1.00  fof(f51,plain,(
% 3.37/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.37/1.00    inference(flattening,[],[f50])).
% 3.37/1.00  
% 3.37/1.00  fof(f62,plain,(
% 3.37/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f61,plain,(
% 3.37/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f60,plain,(
% 3.37/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f59,plain,(
% 3.37/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f63,plain,(
% 3.37/1.00    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.37/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f51,f62,f61,f60,f59])).
% 3.37/1.00  
% 3.37/1.00  fof(f97,plain,(
% 3.37/1.00    m1_pre_topc(sK2,sK1)),
% 3.37/1.00    inference(cnf_transformation,[],[f63])).
% 3.37/1.00  
% 3.37/1.00  fof(f1,axiom,(
% 3.37/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f52,plain,(
% 3.37/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.37/1.00    inference(nnf_transformation,[],[f1])).
% 3.37/1.00  
% 3.37/1.00  fof(f53,plain,(
% 3.37/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.37/1.00    inference(flattening,[],[f52])).
% 3.37/1.00  
% 3.37/1.00  fof(f65,plain,(
% 3.37/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.37/1.00    inference(cnf_transformation,[],[f53])).
% 3.37/1.00  
% 3.37/1.00  fof(f103,plain,(
% 3.37/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.37/1.00    inference(equality_resolution,[],[f65])).
% 3.37/1.00  
% 3.37/1.00  fof(f18,axiom,(
% 3.37/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f48,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.37/1.00    inference(ennf_transformation,[],[f18])).
% 3.37/1.00  
% 3.37/1.00  fof(f49,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.37/1.00    inference(flattening,[],[f48])).
% 3.37/1.00  
% 3.37/1.00  fof(f58,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.37/1.00    inference(nnf_transformation,[],[f49])).
% 3.37/1.00  
% 3.37/1.00  fof(f88,plain,(
% 3.37/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f58])).
% 3.37/1.00  
% 3.37/1.00  fof(f94,plain,(
% 3.37/1.00    v2_pre_topc(sK1)),
% 3.37/1.00    inference(cnf_transformation,[],[f63])).
% 3.37/1.00  
% 3.37/1.00  fof(f95,plain,(
% 3.37/1.00    l1_pre_topc(sK1)),
% 3.37/1.00    inference(cnf_transformation,[],[f63])).
% 3.37/1.00  
% 3.37/1.00  fof(f100,plain,(
% 3.37/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 3.37/1.00    inference(cnf_transformation,[],[f63])).
% 3.37/1.00  
% 3.37/1.00  fof(f6,axiom,(
% 3.37/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f28,plain,(
% 3.37/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.37/1.00    inference(ennf_transformation,[],[f6])).
% 3.37/1.00  
% 3.37/1.00  fof(f29,plain,(
% 3.37/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.37/1.00    inference(flattening,[],[f28])).
% 3.37/1.00  
% 3.37/1.00  fof(f73,plain,(
% 3.37/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f29])).
% 3.37/1.00  
% 3.37/1.00  fof(f5,axiom,(
% 3.37/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f23,plain,(
% 3.37/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.37/1.00    inference(pure_predicate_removal,[],[f5])).
% 3.37/1.00  
% 3.37/1.00  fof(f27,plain,(
% 3.37/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.37/1.00    inference(ennf_transformation,[],[f23])).
% 3.37/1.00  
% 3.37/1.00  fof(f71,plain,(
% 3.37/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.37/1.00    inference(cnf_transformation,[],[f27])).
% 3.37/1.00  
% 3.37/1.00  fof(f7,axiom,(
% 3.37/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f30,plain,(
% 3.37/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.37/1.00    inference(ennf_transformation,[],[f7])).
% 3.37/1.00  
% 3.37/1.00  fof(f31,plain,(
% 3.37/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.37/1.00    inference(flattening,[],[f30])).
% 3.37/1.00  
% 3.37/1.00  fof(f55,plain,(
% 3.37/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.37/1.00    inference(nnf_transformation,[],[f31])).
% 3.37/1.00  
% 3.37/1.00  fof(f74,plain,(
% 3.37/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f55])).
% 3.37/1.00  
% 3.37/1.00  fof(f4,axiom,(
% 3.37/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f26,plain,(
% 3.37/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.37/1.00    inference(ennf_transformation,[],[f4])).
% 3.37/1.00  
% 3.37/1.00  fof(f70,plain,(
% 3.37/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.37/1.00    inference(cnf_transformation,[],[f26])).
% 3.37/1.00  
% 3.37/1.00  fof(f98,plain,(
% 3.37/1.00    v1_funct_1(sK3)),
% 3.37/1.00    inference(cnf_transformation,[],[f63])).
% 3.37/1.00  
% 3.37/1.00  fof(f99,plain,(
% 3.37/1.00    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 3.37/1.00    inference(cnf_transformation,[],[f63])).
% 3.37/1.00  
% 3.37/1.00  fof(f9,axiom,(
% 3.37/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f34,plain,(
% 3.37/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.37/1.00    inference(ennf_transformation,[],[f9])).
% 3.37/1.00  
% 3.37/1.00  fof(f77,plain,(
% 3.37/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f34])).
% 3.37/1.00  
% 3.37/1.00  fof(f11,axiom,(
% 3.37/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f36,plain,(
% 3.37/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.37/1.00    inference(ennf_transformation,[],[f11])).
% 3.37/1.00  
% 3.37/1.00  fof(f37,plain,(
% 3.37/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.37/1.00    inference(flattening,[],[f36])).
% 3.37/1.00  
% 3.37/1.00  fof(f79,plain,(
% 3.37/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f37])).
% 3.37/1.00  
% 3.37/1.00  fof(f90,plain,(
% 3.37/1.00    ~v2_struct_0(sK0)),
% 3.37/1.00    inference(cnf_transformation,[],[f63])).
% 3.37/1.00  
% 3.37/1.00  fof(f92,plain,(
% 3.37/1.00    l1_pre_topc(sK0)),
% 3.37/1.00    inference(cnf_transformation,[],[f63])).
% 3.37/1.00  
% 3.37/1.00  fof(f101,plain,(
% 3.37/1.00    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 3.37/1.00    inference(cnf_transformation,[],[f63])).
% 3.37/1.00  
% 3.37/1.00  fof(f15,axiom,(
% 3.37/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f22,plain,(
% 3.37/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 3.37/1.00    inference(pure_predicate_removal,[],[f15])).
% 3.37/1.00  
% 3.37/1.00  fof(f44,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.37/1.00    inference(ennf_transformation,[],[f22])).
% 3.37/1.00  
% 3.37/1.00  fof(f84,plain,(
% 3.37/1.00    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f44])).
% 3.37/1.00  
% 3.37/1.00  fof(f16,axiom,(
% 3.37/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f45,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 3.37/1.00    inference(ennf_transformation,[],[f16])).
% 3.37/1.00  
% 3.37/1.00  fof(f46,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.37/1.00    inference(flattening,[],[f45])).
% 3.37/1.00  
% 3.37/1.00  fof(f57,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.37/1.00    inference(nnf_transformation,[],[f46])).
% 3.37/1.00  
% 3.37/1.00  fof(f85,plain,(
% 3.37/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f57])).
% 3.37/1.00  
% 3.37/1.00  fof(f108,plain,(
% 3.37/1.00    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 3.37/1.00    inference(equality_resolution,[],[f85])).
% 3.37/1.00  
% 3.37/1.00  fof(f12,axiom,(
% 3.37/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f21,plain,(
% 3.37/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 3.37/1.00    inference(pure_predicate_removal,[],[f12])).
% 3.37/1.00  
% 3.37/1.00  fof(f38,plain,(
% 3.37/1.00    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.37/1.00    inference(ennf_transformation,[],[f21])).
% 3.37/1.00  
% 3.37/1.00  fof(f39,plain,(
% 3.37/1.00    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.37/1.00    inference(flattening,[],[f38])).
% 3.37/1.00  
% 3.37/1.00  fof(f80,plain,(
% 3.37/1.00    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f39])).
% 3.37/1.00  
% 3.37/1.00  fof(f10,axiom,(
% 3.37/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f35,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.37/1.00    inference(ennf_transformation,[],[f10])).
% 3.37/1.00  
% 3.37/1.00  fof(f78,plain,(
% 3.37/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f35])).
% 3.37/1.00  
% 3.37/1.00  fof(f17,axiom,(
% 3.37/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f47,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.37/1.00    inference(ennf_transformation,[],[f17])).
% 3.37/1.00  
% 3.37/1.00  fof(f87,plain,(
% 3.37/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f47])).
% 3.37/1.00  
% 3.37/1.00  fof(f2,axiom,(
% 3.37/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f54,plain,(
% 3.37/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.37/1.00    inference(nnf_transformation,[],[f2])).
% 3.37/1.00  
% 3.37/1.00  fof(f67,plain,(
% 3.37/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.37/1.00    inference(cnf_transformation,[],[f54])).
% 3.37/1.00  
% 3.37/1.00  fof(f89,plain,(
% 3.37/1.00    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f58])).
% 3.37/1.00  
% 3.37/1.00  fof(f66,plain,(
% 3.37/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f53])).
% 3.37/1.00  
% 3.37/1.00  fof(f64,plain,(
% 3.37/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.37/1.00    inference(cnf_transformation,[],[f53])).
% 3.37/1.00  
% 3.37/1.00  fof(f104,plain,(
% 3.37/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.37/1.00    inference(equality_resolution,[],[f64])).
% 3.37/1.00  
% 3.37/1.00  fof(f14,axiom,(
% 3.37/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f42,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.37/1.00    inference(ennf_transformation,[],[f14])).
% 3.37/1.00  
% 3.37/1.00  fof(f43,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/1.00    inference(flattening,[],[f42])).
% 3.37/1.00  
% 3.37/1.00  fof(f83,plain,(
% 3.37/1.00    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f43])).
% 3.37/1.00  
% 3.37/1.00  fof(f8,axiom,(
% 3.37/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f32,plain,(
% 3.37/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.37/1.00    inference(ennf_transformation,[],[f8])).
% 3.37/1.00  
% 3.37/1.00  fof(f33,plain,(
% 3.37/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.37/1.00    inference(flattening,[],[f32])).
% 3.37/1.00  
% 3.37/1.00  fof(f76,plain,(
% 3.37/1.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f33])).
% 3.37/1.00  
% 3.37/1.00  fof(f91,plain,(
% 3.37/1.00    v2_pre_topc(sK0)),
% 3.37/1.00    inference(cnf_transformation,[],[f63])).
% 3.37/1.00  
% 3.37/1.00  fof(f93,plain,(
% 3.37/1.00    ~v2_struct_0(sK1)),
% 3.37/1.00    inference(cnf_transformation,[],[f63])).
% 3.37/1.00  
% 3.37/1.00  fof(f13,axiom,(
% 3.37/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f40,plain,(
% 3.37/1.00    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.37/1.00    inference(ennf_transformation,[],[f13])).
% 3.37/1.00  
% 3.37/1.00  fof(f41,plain,(
% 3.37/1.00    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.37/1.00    inference(flattening,[],[f40])).
% 3.37/1.00  
% 3.37/1.00  fof(f56,plain,(
% 3.37/1.00    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.37/1.00    inference(nnf_transformation,[],[f41])).
% 3.37/1.00  
% 3.37/1.00  fof(f82,plain,(
% 3.37/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f56])).
% 3.37/1.00  
% 3.37/1.00  fof(f106,plain,(
% 3.37/1.00    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.37/1.00    inference(equality_resolution,[],[f82])).
% 3.37/1.00  
% 3.37/1.00  fof(f102,plain,(
% 3.37/1.00    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 3.37/1.00    inference(cnf_transformation,[],[f63])).
% 3.37/1.00  
% 3.37/1.00  fof(f3,axiom,(
% 3.37/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f24,plain,(
% 3.37/1.00    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.37/1.00    inference(ennf_transformation,[],[f3])).
% 3.37/1.00  
% 3.37/1.00  fof(f25,plain,(
% 3.37/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.37/1.00    inference(flattening,[],[f24])).
% 3.37/1.00  
% 3.37/1.00  fof(f69,plain,(
% 3.37/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f25])).
% 3.37/1.00  
% 3.37/1.00  cnf(c_31,negated_conjecture,
% 3.37/1.00      ( m1_pre_topc(sK2,sK1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1967,plain,
% 3.37/1.00      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1,plain,
% 3.37/1.00      ( r1_tarski(X0,X0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1980,plain,
% 3.37/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_25,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ m1_pre_topc(X2,X1)
% 3.37/1.00      | m1_pre_topc(X0,X2)
% 3.37/1.00      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1970,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/1.00      | m1_pre_topc(X2,X1) != iProver_top
% 3.37/1.00      | m1_pre_topc(X0,X2) = iProver_top
% 3.37/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
% 3.37/1.00      | v2_pre_topc(X1) != iProver_top
% 3.37/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3425,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/1.00      | m1_pre_topc(X0,X0) = iProver_top
% 3.37/1.00      | v2_pre_topc(X1) != iProver_top
% 3.37/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_1980,c_1970]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6554,plain,
% 3.37/1.00      ( m1_pre_topc(sK2,sK2) = iProver_top
% 3.37/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_1967,c_3425]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_34,negated_conjecture,
% 3.37/1.00      ( v2_pre_topc(sK1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_43,plain,
% 3.37/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_33,negated_conjecture,
% 3.37/1.00      ( l1_pre_topc(sK1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_44,plain,
% 3.37/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_46,plain,
% 3.37/1.00      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2274,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,sK1)
% 3.37/1.00      | m1_pre_topc(sK2,X0)
% 3.37/1.00      | ~ m1_pre_topc(sK2,sK1)
% 3.37/1.00      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 3.37/1.00      | ~ v2_pre_topc(sK1)
% 3.37/1.00      | ~ l1_pre_topc(sK1) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2455,plain,
% 3.37/1.00      ( m1_pre_topc(sK2,sK2)
% 3.37/1.00      | ~ m1_pre_topc(sK2,sK1)
% 3.37/1.00      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2))
% 3.37/1.00      | ~ v2_pre_topc(sK1)
% 3.37/1.00      | ~ l1_pre_topc(sK1) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_2274]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2456,plain,
% 3.37/1.00      ( m1_pre_topc(sK2,sK2) = iProver_top
% 3.37/1.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.37/1.00      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.37/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_2455]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2819,plain,
% 3.37/1.00      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2820,plain,
% 3.37/1.00      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_2819]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6598,plain,
% 3.37/1.00      ( m1_pre_topc(sK2,sK2) = iProver_top ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_6554,c_43,c_44,c_46,c_2456,c_2820]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_28,negated_conjecture,
% 3.37/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 3.37/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1969,plain,
% 3.37/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_8,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.37/1.00      | v1_partfun1(X0,X1)
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.00      | v1_xboole_0(X2)
% 3.37/1.00      | ~ v1_funct_1(X0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_7,plain,
% 3.37/1.00      ( v4_relat_1(X0,X1)
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.37/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_11,plain,
% 3.37/1.00      ( ~ v1_partfun1(X0,X1)
% 3.37/1.00      | ~ v4_relat_1(X0,X1)
% 3.37/1.00      | ~ v1_relat_1(X0)
% 3.37/1.00      | k1_relat_1(X0) = X1 ),
% 3.37/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_513,plain,
% 3.37/1.00      ( ~ v1_partfun1(X0,X1)
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.00      | ~ v1_relat_1(X0)
% 3.37/1.00      | k1_relat_1(X0) = X1 ),
% 3.37/1.00      inference(resolution,[status(thm)],[c_7,c_11]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.00      | v1_relat_1(X0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_517,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.00      | ~ v1_partfun1(X0,X1)
% 3.37/1.00      | k1_relat_1(X0) = X1 ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_513,c_11,c_7,c_6]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_518,plain,
% 3.37/1.00      ( ~ v1_partfun1(X0,X1)
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.00      | k1_relat_1(X0) = X1 ),
% 3.37/1.00      inference(renaming,[status(thm)],[c_517]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_574,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.37/1.00      | v1_xboole_0(X2)
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | k1_relat_1(X0) = X1 ),
% 3.37/1.00      inference(resolution,[status(thm)],[c_8,c_518]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_578,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.00      | ~ v1_funct_2(X0,X1,X2)
% 3.37/1.00      | v1_xboole_0(X2)
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | k1_relat_1(X0) = X1 ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_574,c_11,c_8,c_7,c_6]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_579,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.00      | v1_xboole_0(X2)
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | k1_relat_1(X0) = X1 ),
% 3.37/1.00      inference(renaming,[status(thm)],[c_578]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_30,negated_conjecture,
% 3.37/1.00      ( v1_funct_1(sK3) ),
% 3.37/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_712,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.00      | v1_xboole_0(X2)
% 3.37/1.00      | k1_relat_1(X0) = X1
% 3.37/1.00      | sK3 != X0 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_579,c_30]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_713,plain,
% 3.37/1.00      ( ~ v1_funct_2(sK3,X0,X1)
% 3.37/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.37/1.00      | v1_xboole_0(X1)
% 3.37/1.00      | k1_relat_1(sK3) = X0 ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_712]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1957,plain,
% 3.37/1.00      ( k1_relat_1(sK3) = X0
% 3.37/1.00      | v1_funct_2(sK3,X0,X1) != iProver_top
% 3.37/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.37/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2604,plain,
% 3.37/1.00      ( u1_struct_0(sK1) = k1_relat_1(sK3)
% 3.37/1.00      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_1969,c_1957]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_29,negated_conjecture,
% 3.37/1.00      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 3.37/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_48,plain,
% 3.37/1.00      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2710,plain,
% 3.37/1.00      ( u1_struct_0(sK1) = k1_relat_1(sK3)
% 3.37/1.00      | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_2604,c_48]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_13,plain,
% 3.37/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_15,plain,
% 3.37/1.00      ( v2_struct_0(X0)
% 3.37/1.00      | ~ l1_struct_0(X0)
% 3.37/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.37/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_495,plain,
% 3.37/1.00      ( v2_struct_0(X0)
% 3.37/1.00      | ~ l1_pre_topc(X0)
% 3.37/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.37/1.00      inference(resolution,[status(thm)],[c_13,c_15]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1958,plain,
% 3.37/1.00      ( v2_struct_0(X0) = iProver_top
% 3.37/1.00      | l1_pre_topc(X0) != iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2836,plain,
% 3.37/1.00      ( u1_struct_0(sK1) = k1_relat_1(sK3)
% 3.37/1.00      | v2_struct_0(sK0) = iProver_top
% 3.37/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_2710,c_1958]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_38,negated_conjecture,
% 3.37/1.00      ( ~ v2_struct_0(sK0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_39,plain,
% 3.37/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_36,negated_conjecture,
% 3.37/1.00      ( l1_pre_topc(sK0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_41,plain,
% 3.37/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3162,plain,
% 3.37/1.00      ( u1_struct_0(sK1) = k1_relat_1(sK3) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_2836,c_39,c_41]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_27,negated_conjecture,
% 3.37/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.37/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3170,plain,
% 3.37/1.00      ( g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.37/1.00      inference(demodulation,[status(thm)],[c_3162,c_27]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_20,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.37/1.00      | ~ l1_pre_topc(X1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1973,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/1.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 3.37/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4093,plain,
% 3.37/1.00      ( m1_pre_topc(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)),X0) = iProver_top
% 3.37/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 3.37/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_3170,c_1973]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_22,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.37/1.00      | ~ v2_pre_topc(X0)
% 3.37/1.00      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X0)
% 3.37/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.37/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_16,plain,
% 3.37/1.00      ( ~ v2_pre_topc(X0)
% 3.37/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.37/1.00      | ~ l1_pre_topc(X0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_213,plain,
% 3.37/1.00      ( ~ v2_pre_topc(X0)
% 3.37/1.00      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.37/1.00      | m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X0)
% 3.37/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_22,c_16]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_214,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.37/1.00      | ~ v2_pre_topc(X0)
% 3.37/1.00      | ~ l1_pre_topc(X0)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.37/1.00      inference(renaming,[status(thm)],[c_213]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1959,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1) = iProver_top
% 3.37/1.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 3.37/1.00      | v2_pre_topc(X0) != iProver_top
% 3.37/1.00      | l1_pre_topc(X1) != iProver_top
% 3.37/1.00      | l1_pre_topc(X0) != iProver_top
% 3.37/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_214]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_14,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1975,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/1.00      | l1_pre_topc(X1) != iProver_top
% 3.37/1.00      | l1_pre_topc(X0) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2102,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1) = iProver_top
% 3.37/1.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 3.37/1.00      | v2_pre_topc(X0) != iProver_top
% 3.37/1.00      | l1_pre_topc(X1) != iProver_top
% 3.37/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.37/1.00      inference(forward_subsumption_resolution,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_1959,c_1975]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4892,plain,
% 3.37/1.00      ( m1_pre_topc(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)),X0) != iProver_top
% 3.37/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 3.37/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.37/1.00      | l1_pre_topc(X0) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_3162,c_2102]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_7164,plain,
% 3.37/1.00      ( l1_pre_topc(X0) != iProver_top
% 3.37/1.00      | m1_pre_topc(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)),X0) != iProver_top
% 3.37/1.00      | m1_pre_topc(sK1,X0) = iProver_top ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_4892,c_43,c_44]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_7165,plain,
% 3.37/1.00      ( m1_pre_topc(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)),X0) != iProver_top
% 3.37/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 3.37/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.37/1.00      inference(renaming,[status(thm)],[c_7164]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_7174,plain,
% 3.37/1.00      ( m1_pre_topc(sK2,X0) != iProver_top
% 3.37/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 3.37/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_4093,c_7165]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_7195,plain,
% 3.37/1.00      ( m1_pre_topc(sK1,sK2) = iProver_top
% 3.37/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_6598,c_7174]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2974,plain,
% 3.37/1.00      ( l1_pre_topc(sK2) = iProver_top
% 3.37/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_1967,c_1975]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_7733,plain,
% 3.37/1.00      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_7195,c_44,c_2974]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_23,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | ~ l1_pre_topc(X1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1972,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.37/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1978,plain,
% 3.37/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.37/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3670,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.37/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_1972,c_1978]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_24,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ m1_pre_topc(X2,X1)
% 3.37/1.00      | ~ m1_pre_topc(X0,X2)
% 3.37/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1971,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/1.00      | m1_pre_topc(X2,X1) != iProver_top
% 3.37/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 3.37/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 3.37/1.00      | v2_pre_topc(X1) != iProver_top
% 3.37/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4087,plain,
% 3.37/1.00      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.37/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 3.37/1.00      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 3.37/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_1967,c_1971]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4310,plain,
% 3.37/1.00      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.37/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 3.37/1.00      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_4087,c_43,c_44]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_0,plain,
% 3.37/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.37/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1981,plain,
% 3.37/1.00      ( X0 = X1
% 3.37/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.37/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4320,plain,
% 3.37/1.00      ( u1_struct_0(X0) = u1_struct_0(sK2)
% 3.37/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 3.37/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 3.37/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_4310,c_1981]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5004,plain,
% 3.37/1.00      ( u1_struct_0(X0) = u1_struct_0(sK2)
% 3.37/1.00      | m1_pre_topc(X0,sK2) != iProver_top
% 3.37/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 3.37/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_3670,c_4320]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6403,plain,
% 3.37/1.00      ( m1_pre_topc(sK2,X0) != iProver_top
% 3.37/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 3.37/1.00      | m1_pre_topc(X0,sK2) != iProver_top
% 3.37/1.00      | u1_struct_0(X0) = u1_struct_0(sK2) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_5004,c_44,c_2974]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6404,plain,
% 3.37/1.00      ( u1_struct_0(X0) = u1_struct_0(sK2)
% 3.37/1.00      | m1_pre_topc(X0,sK2) != iProver_top
% 3.37/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 3.37/1.00      | m1_pre_topc(sK2,X0) != iProver_top ),
% 3.37/1.00      inference(renaming,[status(thm)],[c_6403]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6413,plain,
% 3.37/1.00      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 3.37/1.00      | m1_pre_topc(sK1,sK2) != iProver_top
% 3.37/1.00      | m1_pre_topc(sK1,sK1) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_1967,c_6404]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6414,plain,
% 3.37/1.00      ( u1_struct_0(sK2) = k1_relat_1(sK3)
% 3.37/1.00      | m1_pre_topc(sK1,sK2) != iProver_top
% 3.37/1.00      | m1_pre_topc(sK1,sK1) != iProver_top ),
% 3.37/1.00      inference(light_normalisation,[status(thm)],[c_6413,c_3162]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_58,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1) = iProver_top
% 3.37/1.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 3.37/1.00      | v2_pre_topc(X0) != iProver_top
% 3.37/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 3.37/1.00      | l1_pre_topc(X1) != iProver_top
% 3.37/1.00      | l1_pre_topc(X0) != iProver_top
% 3.37/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_60,plain,
% 3.37/1.00      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
% 3.37/1.00      | m1_pre_topc(sK1,sK1) = iProver_top
% 3.37/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.37/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.37/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_58]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_76,plain,
% 3.37/1.00      ( v2_pre_topc(X0) != iProver_top
% 3.37/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 3.37/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_78,plain,
% 3.37/1.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.37/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_76]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2,plain,
% 3.37/1.00      ( r1_tarski(X0,X0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_115,plain,
% 3.37/1.00      ( r1_tarski(sK1,sK1) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_119,plain,
% 3.37/1.00      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2249,plain,
% 3.37/1.00      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
% 3.37/1.00      | ~ m1_pre_topc(sK2,sK1)
% 3.37/1.00      | ~ l1_pre_topc(sK1) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2250,plain,
% 3.37/1.00      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) = iProver_top
% 3.37/1.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_2249]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2277,plain,
% 3.37/1.00      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2278,plain,
% 3.37/1.00      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 3.37/1.00      | l1_pre_topc(X1) != iProver_top
% 3.37/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_2277]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2280,plain,
% 3.37/1.00      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
% 3.37/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.37/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_2278]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1231,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.37/1.00      theory(equality) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2309,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
% 3.37/1.00      | X0 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 3.37/1.00      | X1 != sK1 ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_1231]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2627,plain,
% 3.37/1.00      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
% 3.37/1.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
% 3.37/1.00      | X0 != sK1
% 3.37/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_2309]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2628,plain,
% 3.37/1.00      ( X0 != sK1
% 3.37/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 3.37/1.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
% 3.37/1.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_2627]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2630,plain,
% 3.37/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 3.37/1.00      | sK1 != sK1
% 3.37/1.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
% 3.37/1.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_2628]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6833,plain,
% 3.37/1.00      ( m1_pre_topc(sK1,sK2) != iProver_top
% 3.37/1.00      | u1_struct_0(sK2) = k1_relat_1(sK3) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_6414,c_43,c_44,c_46,c_27,c_60,c_78,c_115,c_119,c_2250,
% 3.37/1.00                 c_2280,c_2630]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6834,plain,
% 3.37/1.00      ( u1_struct_0(sK2) = k1_relat_1(sK3)
% 3.37/1.00      | m1_pre_topc(sK1,sK2) != iProver_top ),
% 3.37/1.00      inference(renaming,[status(thm)],[c_6833]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_7747,plain,
% 3.37/1.00      ( u1_struct_0(sK2) = k1_relat_1(sK3) ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_7733,c_6834]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_19,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.37/1.00      | ~ m1_pre_topc(X3,X1)
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ v2_pre_topc(X2)
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | v2_struct_0(X2)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X2)
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.37/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_730,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.37/1.00      | ~ m1_pre_topc(X3,X1)
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ v2_pre_topc(X2)
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | v2_struct_0(X2)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X2)
% 3.37/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 3.37/1.00      | sK3 != X0 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_731,plain,
% 3.37/1.00      ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
% 3.37/1.00      | ~ m1_pre_topc(X2,X0)
% 3.37/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.37/1.00      | ~ v2_pre_topc(X0)
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | v2_struct_0(X0)
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | ~ l1_pre_topc(X0)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2) ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_730]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1956,plain,
% 3.37/1.00      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2)
% 3.37/1.00      | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.37/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 3.37/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.37/1.00      | v2_pre_topc(X1) != iProver_top
% 3.37/1.00      | v2_pre_topc(X0) != iProver_top
% 3.37/1.00      | v2_struct_0(X1) = iProver_top
% 3.37/1.00      | v2_struct_0(X0) = iProver_top
% 3.37/1.00      | l1_pre_topc(X1) != iProver_top
% 3.37/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2727,plain,
% 3.37/1.00      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 3.37/1.00      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.37/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 3.37/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.37/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.37/1.00      | v2_struct_0(sK0) = iProver_top
% 3.37/1.00      | v2_struct_0(sK1) = iProver_top
% 3.37/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_1969,c_1956]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_12,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.37/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_766,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 3.37/1.00      | sK3 != X0 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_30]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_767,plain,
% 3.37/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.37/1.00      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_766]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1955,plain,
% 3.37/1.00      ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 3.37/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_767]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2498,plain,
% 3.37/1.00      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_1969,c_1955]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2728,plain,
% 3.37/1.00      ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
% 3.37/1.00      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.37/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 3.37/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.37/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.37/1.00      | v2_struct_0(sK0) = iProver_top
% 3.37/1.00      | v2_struct_0(sK1) = iProver_top
% 3.37/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.37/1.00      inference(demodulation,[status(thm)],[c_2727,c_2498]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_37,negated_conjecture,
% 3.37/1.00      ( v2_pre_topc(sK0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_40,plain,
% 3.37/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_35,negated_conjecture,
% 3.37/1.00      ( ~ v2_struct_0(sK1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_42,plain,
% 3.37/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2797,plain,
% 3.37/1.00      ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
% 3.37/1.00      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_2728,c_39,c_40,c_41,c_42,c_43,c_44,c_48]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2805,plain,
% 3.37/1.00      ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_1967,c_2797]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_17,plain,
% 3.37/1.00      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 3.37/1.00      | ~ v1_funct_2(X4,X2,X3)
% 3.37/1.00      | ~ v1_funct_2(X4,X0,X1)
% 3.37/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.37/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.37/1.00      | v1_xboole_0(X1)
% 3.37/1.00      | v1_xboole_0(X3)
% 3.37/1.00      | ~ v1_funct_1(X4) ),
% 3.37/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_26,negated_conjecture,
% 3.37/1.00      ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
% 3.37/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_608,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.37/1.00      | ~ v1_funct_2(X0,X3,X4)
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.37/1.00      | v1_xboole_0(X4)
% 3.37/1.00      | v1_xboole_0(X2)
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | k2_tmap_1(sK1,sK0,sK3,sK2) != X0
% 3.37/1.00      | u1_struct_0(sK2) != X1
% 3.37/1.00      | u1_struct_0(sK0) != X2
% 3.37/1.00      | u1_struct_0(sK0) != X4
% 3.37/1.00      | u1_struct_0(sK1) != X3
% 3.37/1.00      | sK3 != X0 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_609,plain,
% 3.37/1.00      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 3.37/1.00      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.37/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 3.37/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.37/1.00      | v1_xboole_0(u1_struct_0(sK0))
% 3.37/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 3.37/1.00      | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_608]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_778,plain,
% 3.37/1.00      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 3.37/1.00      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.37/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 3.37/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.37/1.00      | v1_xboole_0(u1_struct_0(sK0))
% 3.37/1.00      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_609]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1954,plain,
% 3.37/1.00      ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 3.37/1.00      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.37/1.00      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.37/1.00      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.37/1.00      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_778]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2807,plain,
% 3.37/1.00      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 3.37/1.00      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.37/1.00      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.37/1.00      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.37/1.00      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
% 3.37/1.00      inference(demodulation,[status(thm)],[c_2805,c_1954]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3166,plain,
% 3.37/1.00      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 3.37/1.00      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.37/1.00      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 3.37/1.00      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.37/1.00      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
% 3.37/1.00      inference(demodulation,[status(thm)],[c_3162,c_2807]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3056,plain,
% 3.37/1.00      ( v2_struct_0(sK0)
% 3.37/1.00      | ~ l1_pre_topc(sK0)
% 3.37/1.00      | ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_495]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3057,plain,
% 3.37/1.00      ( v2_struct_0(sK0) = iProver_top
% 3.37/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(sK0)) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_3056]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5642,plain,
% 3.37/1.00      ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top
% 3.37/1.00      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.37/1.00      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 3.37/1.00      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.37/1.00      | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_3166,c_39,c_41,c_3057]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5643,plain,
% 3.37/1.00      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 3.37/1.00      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.37/1.00      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 3.37/1.00      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.37/1.00      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
% 3.37/1.00      inference(renaming,[status(thm)],[c_5642]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_8006,plain,
% 3.37/1.00      ( k7_relat_1(sK3,k1_relat_1(sK3)) != sK3
% 3.37/1.00      | v1_funct_2(k7_relat_1(sK3,k1_relat_1(sK3)),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 3.37/1.00      | m1_subset_1(k7_relat_1(sK3,k1_relat_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
% 3.37/1.00      inference(demodulation,[status(thm)],[c_7747,c_5643]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1976,plain,
% 3.37/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.37/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2959,plain,
% 3.37/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_1969,c_1976]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5,plain,
% 3.37/1.00      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.37/1.00      | ~ v1_relat_1(X0)
% 3.37/1.00      | k7_relat_1(X0,X1) = X0 ),
% 3.37/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1977,plain,
% 3.37/1.00      ( k7_relat_1(X0,X1) = X0
% 3.37/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.37/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3558,plain,
% 3.37/1.00      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 3.37/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_1980,c_1977]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4206,plain,
% 3.37/1.00      ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_2959,c_3558]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_8058,plain,
% 3.37/1.00      ( sK3 != sK3
% 3.37/1.00      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 3.37/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
% 3.37/1.00      inference(light_normalisation,[status(thm)],[c_8006,c_4206]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_8059,plain,
% 3.37/1.00      ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 3.37/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
% 3.37/1.00      inference(equality_resolution_simp,[status(thm)],[c_8058]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1968,plain,
% 3.37/1.00      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3169,plain,
% 3.37/1.00      ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) = iProver_top ),
% 3.37/1.00      inference(demodulation,[status(thm)],[c_3162,c_1968]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3168,plain,
% 3.37/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) = iProver_top ),
% 3.37/1.00      inference(demodulation,[status(thm)],[c_3162,c_1969]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(contradiction,plain,
% 3.37/1.00      ( $false ),
% 3.37/1.00      inference(minisat,[status(thm)],[c_8059,c_3169,c_3168]) ).
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.37/1.00  
% 3.37/1.00  ------                               Statistics
% 3.37/1.00  
% 3.37/1.00  ------ General
% 3.37/1.00  
% 3.37/1.00  abstr_ref_over_cycles:                  0
% 3.37/1.00  abstr_ref_under_cycles:                 0
% 3.37/1.00  gc_basic_clause_elim:                   0
% 3.37/1.00  forced_gc_time:                         0
% 3.37/1.00  parsing_time:                           0.012
% 3.37/1.00  unif_index_cands_time:                  0.
% 3.37/1.00  unif_index_add_time:                    0.
% 3.37/1.00  orderings_time:                         0.
% 3.37/1.00  out_proof_time:                         0.016
% 3.37/1.00  total_time:                             0.25
% 3.37/1.00  num_of_symbols:                         58
% 3.37/1.00  num_of_terms:                           4587
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing
% 3.37/1.00  
% 3.37/1.00  num_of_splits:                          0
% 3.37/1.00  num_of_split_atoms:                     0
% 3.37/1.00  num_of_reused_defs:                     0
% 3.37/1.00  num_eq_ax_congr_red:                    12
% 3.37/1.00  num_of_sem_filtered_clauses:            1
% 3.37/1.00  num_of_subtypes:                        0
% 3.37/1.00  monotx_restored_types:                  0
% 3.37/1.00  sat_num_of_epr_types:                   0
% 3.37/1.00  sat_num_of_non_cyclic_types:            0
% 3.37/1.00  sat_guarded_non_collapsed_types:        0
% 3.37/1.00  num_pure_diseq_elim:                    0
% 3.37/1.00  simp_replaced_by:                       0
% 3.37/1.00  res_preprocessed:                       162
% 3.37/1.00  prep_upred:                             0
% 3.37/1.00  prep_unflattend:                        21
% 3.37/1.00  smt_new_axioms:                         0
% 3.37/1.00  pred_elim_cands:                        9
% 3.37/1.00  pred_elim:                              5
% 3.37/1.00  pred_elim_cl:                           7
% 3.37/1.00  pred_elim_cycles:                       10
% 3.37/1.00  merged_defs:                            8
% 3.37/1.00  merged_defs_ncl:                        0
% 3.37/1.00  bin_hyper_res:                          8
% 3.37/1.00  prep_cycles:                            4
% 3.37/1.00  pred_elim_time:                         0.012
% 3.37/1.00  splitting_time:                         0.
% 3.37/1.00  sem_filter_time:                        0.
% 3.37/1.00  monotx_time:                            0.
% 3.37/1.00  subtype_inf_time:                       0.
% 3.37/1.00  
% 3.37/1.00  ------ Problem properties
% 3.37/1.00  
% 3.37/1.00  clauses:                                29
% 3.37/1.00  conjectures:                            11
% 3.37/1.00  epr:                                    11
% 3.37/1.00  horn:                                   27
% 3.37/1.00  ground:                                 12
% 3.37/1.00  unary:                                  12
% 3.37/1.00  binary:                                 4
% 3.37/1.00  lits:                                   79
% 3.37/1.00  lits_eq:                                7
% 3.37/1.00  fd_pure:                                0
% 3.37/1.00  fd_pseudo:                              0
% 3.37/1.00  fd_cond:                                1
% 3.37/1.00  fd_pseudo_cond:                         1
% 3.37/1.00  ac_symbols:                             0
% 3.37/1.00  
% 3.37/1.00  ------ Propositional Solver
% 3.37/1.00  
% 3.37/1.00  prop_solver_calls:                      29
% 3.37/1.00  prop_fast_solver_calls:                 1459
% 3.37/1.00  smt_solver_calls:                       0
% 3.37/1.00  smt_fast_solver_calls:                  0
% 3.37/1.00  prop_num_of_clauses:                    2392
% 3.37/1.00  prop_preprocess_simplified:             7139
% 3.37/1.00  prop_fo_subsumed:                       74
% 3.37/1.00  prop_solver_time:                       0.
% 3.37/1.00  smt_solver_time:                        0.
% 3.37/1.00  smt_fast_solver_time:                   0.
% 3.37/1.00  prop_fast_solver_time:                  0.
% 3.37/1.00  prop_unsat_core_time:                   0.
% 3.37/1.00  
% 3.37/1.00  ------ QBF
% 3.37/1.00  
% 3.37/1.00  qbf_q_res:                              0
% 3.37/1.00  qbf_num_tautologies:                    0
% 3.37/1.00  qbf_prep_cycles:                        0
% 3.37/1.00  
% 3.37/1.00  ------ BMC1
% 3.37/1.00  
% 3.37/1.00  bmc1_current_bound:                     -1
% 3.37/1.00  bmc1_last_solved_bound:                 -1
% 3.37/1.00  bmc1_unsat_core_size:                   -1
% 3.37/1.00  bmc1_unsat_core_parents_size:           -1
% 3.37/1.00  bmc1_merge_next_fun:                    0
% 3.37/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.37/1.00  
% 3.37/1.00  ------ Instantiation
% 3.37/1.00  
% 3.37/1.00  inst_num_of_clauses:                    727
% 3.37/1.00  inst_num_in_passive:                    147
% 3.37/1.00  inst_num_in_active:                     490
% 3.37/1.00  inst_num_in_unprocessed:                91
% 3.37/1.00  inst_num_of_loops:                      520
% 3.37/1.00  inst_num_of_learning_restarts:          0
% 3.37/1.00  inst_num_moves_active_passive:          26
% 3.37/1.00  inst_lit_activity:                      0
% 3.37/1.00  inst_lit_activity_moves:                0
% 3.37/1.00  inst_num_tautologies:                   0
% 3.37/1.00  inst_num_prop_implied:                  0
% 3.37/1.00  inst_num_existing_simplified:           0
% 3.37/1.00  inst_num_eq_res_simplified:             0
% 3.37/1.00  inst_num_child_elim:                    0
% 3.37/1.00  inst_num_of_dismatching_blockings:      342
% 3.37/1.00  inst_num_of_non_proper_insts:           1165
% 3.37/1.00  inst_num_of_duplicates:                 0
% 3.37/1.00  inst_inst_num_from_inst_to_res:         0
% 3.37/1.00  inst_dismatching_checking_time:         0.
% 3.37/1.00  
% 3.37/1.00  ------ Resolution
% 3.37/1.00  
% 3.37/1.00  res_num_of_clauses:                     0
% 3.37/1.00  res_num_in_passive:                     0
% 3.37/1.00  res_num_in_active:                      0
% 3.37/1.00  res_num_of_loops:                       166
% 3.37/1.00  res_forward_subset_subsumed:            129
% 3.37/1.00  res_backward_subset_subsumed:           6
% 3.37/1.00  res_forward_subsumed:                   0
% 3.37/1.00  res_backward_subsumed:                  0
% 3.37/1.00  res_forward_subsumption_resolution:     1
% 3.37/1.00  res_backward_subsumption_resolution:    0
% 3.37/1.00  res_clause_to_clause_subsumption:       465
% 3.37/1.00  res_orphan_elimination:                 0
% 3.37/1.00  res_tautology_del:                      102
% 3.37/1.00  res_num_eq_res_simplified:              0
% 3.37/1.00  res_num_sel_changes:                    0
% 3.37/1.00  res_moves_from_active_to_pass:          0
% 3.37/1.00  
% 3.37/1.00  ------ Superposition
% 3.37/1.00  
% 3.37/1.00  sup_time_total:                         0.
% 3.37/1.00  sup_time_generating:                    0.
% 3.37/1.00  sup_time_sim_full:                      0.
% 3.37/1.00  sup_time_sim_immed:                     0.
% 3.37/1.00  
% 3.37/1.00  sup_num_of_clauses:                     124
% 3.37/1.00  sup_num_in_active:                      78
% 3.37/1.00  sup_num_in_passive:                     46
% 3.37/1.00  sup_num_of_loops:                       102
% 3.37/1.00  sup_fw_superposition:                   102
% 3.37/1.00  sup_bw_superposition:                   95
% 3.37/1.00  sup_immediate_simplified:               73
% 3.37/1.00  sup_given_eliminated:                   0
% 3.37/1.00  comparisons_done:                       0
% 3.37/1.00  comparisons_avoided:                    0
% 3.37/1.00  
% 3.37/1.00  ------ Simplifications
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  sim_fw_subset_subsumed:                 18
% 3.37/1.00  sim_bw_subset_subsumed:                 12
% 3.37/1.00  sim_fw_subsumed:                        30
% 3.37/1.00  sim_bw_subsumed:                        1
% 3.37/1.00  sim_fw_subsumption_res:                 4
% 3.37/1.00  sim_bw_subsumption_res:                 0
% 3.37/1.00  sim_tautology_del:                      13
% 3.37/1.00  sim_eq_tautology_del:                   11
% 3.37/1.00  sim_eq_res_simp:                        1
% 3.37/1.00  sim_fw_demodulated:                     3
% 3.37/1.00  sim_bw_demodulated:                     21
% 3.37/1.00  sim_light_normalised:                   37
% 3.37/1.00  sim_joinable_taut:                      0
% 3.37/1.00  sim_joinable_simp:                      0
% 3.37/1.00  sim_ac_normalised:                      0
% 3.37/1.00  sim_smt_subsumption:                    0
% 3.37/1.00  
%------------------------------------------------------------------------------
