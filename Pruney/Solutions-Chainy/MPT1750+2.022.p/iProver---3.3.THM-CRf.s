%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:26 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  229 (1114 expanded)
%              Number of clauses        :  138 ( 315 expanded)
%              Number of leaves         :   22 ( 335 expanded)
%              Depth                    :   26
%              Number of atoms          :  959 (9645 expanded)
%              Number of equality atoms :  335 (1360 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   4 average)
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
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,
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

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f45,f55,f54,f53,f52])).

fof(f86,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f39])).

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
    inference(nnf_transformation,[],[f40])).

fof(f74,plain,(
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
    inference(equality_resolution,[],[f74])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f69,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f84,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f16,axiom,(
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

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f56])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f36])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f80,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f81,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f82,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f94,plain,(
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
    inference(equality_resolution,[],[f71])).

fof(f91,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1586,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1592,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3148,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_1592])).

cnf(c_18,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_12,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_191,plain,
    ( ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_12])).

cnf(c_192,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(renaming,[status(thm)],[c_191])).

cnf(c_1578,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_192])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1594,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1707,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1578,c_1594])).

cnf(c_4387,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK1,X0) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3148,c_1707])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_39,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_40,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4880,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK1,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4387,c_39,c_40])).

cnf(c_4881,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK1,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4880])).

cnf(c_4889,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1586,c_4881])).

cnf(c_42,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_54,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_56,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
    | m1_pre_topc(sK1,sK1) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_72,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_74,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_101,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_105,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1834,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1835,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1834])).

cnf(c_1874,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1875,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1874])).

cnf(c_1877,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1875])).

cnf(c_904,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1892,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
    | X0 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_904])).

cnf(c_2147,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
    | X0 != sK1
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_1892])).

cnf(c_2148,plain,
    ( X0 != sK1
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2147])).

cnf(c_2150,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | sK1 != sK1
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2148])).

cnf(c_4966,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4889,c_39,c_40,c_42,c_23,c_56,c_74,c_101,c_105,c_1835,c_1877,c_2150])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1590,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4975,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4966,c_1590])).

cnf(c_5641,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4975,c_39,c_40])).

cnf(c_1598,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5650,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK1)
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5641,c_1598])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1591,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1595,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3140,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1591,c_1595])).

cnf(c_3714,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3140,c_1598])).

cnf(c_5652,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK1)
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5641,c_3714])).

cnf(c_7524,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5650,c_40,c_5652])).

cnf(c_7525,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK1)
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7524])).

cnf(c_7532,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_pre_topc(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1586,c_7525])).

cnf(c_1862,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_pre_topc(sK2,sK1)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1863,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1862])).

cnf(c_1865,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1863])).

cnf(c_2639,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1586,c_1594])).

cnf(c_3546,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK2))
    | ~ r1_tarski(u1_struct_0(sK2),X0)
    | u1_struct_0(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4487,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | u1_struct_0(sK2) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_3546])).

cnf(c_4489,plain,
    ( u1_struct_0(sK2) = u1_struct_0(X0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4487])).

cnf(c_4491,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4489])).

cnf(c_4488,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(sK2,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_4493,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4488])).

cnf(c_4495,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4493])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1597,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1589,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) = iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2992,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1597,c_1589])).

cnf(c_3816,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1586,c_2992])).

cnf(c_1867,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | m1_pre_topc(sK2,X0)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2417,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1867])).

cnf(c_2418,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2417])).

cnf(c_2601,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2602,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2601])).

cnf(c_3848,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3816,c_39,c_40,c_42,c_2418,c_2602])).

cnf(c_4890,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3848,c_4881])).

cnf(c_7550,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7532,c_39,c_40,c_42,c_23,c_56,c_74,c_101,c_105,c_1835,c_1865,c_1877,c_2150,c_2639,c_4491,c_4495,c_4890])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1588,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f72])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_563,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_564,plain,
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
    inference(unflattening,[status(thm)],[c_563])).

cnf(c_1576,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_564])).

cnf(c_2347,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1588,c_1576])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_599,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_26])).

cnf(c_600,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_599])).

cnf(c_1575,plain,
    ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_600])).

cnf(c_2140,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1588,c_1575])).

cnf(c_2348,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2347,c_2140])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_35,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_36,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_37,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_38,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_44,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2388,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2348,c_35,c_36,c_37,c_38,c_39,c_40,c_44])).

cnf(c_2396,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_1586,c_2388])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_468,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_9,c_11])).

cnf(c_13,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_22,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_488,plain,
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
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_489,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_521,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_468,c_489])).

cnf(c_611,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_26,c_521])).

cnf(c_893,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | sP0_iProver_split
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_611])).

cnf(c_1573,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_893])).

cnf(c_2398,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2396,c_1573])).

cnf(c_892,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_611])).

cnf(c_1574,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK0)
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_892])).

cnf(c_2242,plain,
    ( v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1574])).

cnf(c_2431,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2398,c_35,c_37,c_2242])).

cnf(c_2432,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2431])).

cnf(c_7557,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7550,c_2432])).

cnf(c_7,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_7,c_5])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_452,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_448,c_7,c_6,c_5])).

cnf(c_1577,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_2443,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
    inference(superposition,[status(thm)],[c_1588,c_1577])).

cnf(c_7568,plain,
    ( sK3 != sK3
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7557,c_2443])).

cnf(c_7569,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7568])).

cnf(c_45,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7569,c_45,c_44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:56:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.99/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/0.98  
% 2.99/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.99/0.98  
% 2.99/0.98  ------  iProver source info
% 2.99/0.98  
% 2.99/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.99/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.99/0.98  git: non_committed_changes: false
% 2.99/0.98  git: last_make_outside_of_git: false
% 2.99/0.98  
% 2.99/0.98  ------ 
% 2.99/0.98  
% 2.99/0.98  ------ Input Options
% 2.99/0.98  
% 2.99/0.98  --out_options                           all
% 2.99/0.98  --tptp_safe_out                         true
% 2.99/0.98  --problem_path                          ""
% 2.99/0.98  --include_path                          ""
% 2.99/0.98  --clausifier                            res/vclausify_rel
% 2.99/0.98  --clausifier_options                    --mode clausify
% 2.99/0.98  --stdin                                 false
% 2.99/0.98  --stats_out                             all
% 2.99/0.98  
% 2.99/0.98  ------ General Options
% 2.99/0.98  
% 2.99/0.98  --fof                                   false
% 2.99/0.98  --time_out_real                         305.
% 2.99/0.98  --time_out_virtual                      -1.
% 2.99/0.98  --symbol_type_check                     false
% 2.99/0.98  --clausify_out                          false
% 2.99/0.98  --sig_cnt_out                           false
% 2.99/0.98  --trig_cnt_out                          false
% 2.99/0.98  --trig_cnt_out_tolerance                1.
% 2.99/0.98  --trig_cnt_out_sk_spl                   false
% 2.99/0.98  --abstr_cl_out                          false
% 2.99/0.98  
% 2.99/0.98  ------ Global Options
% 2.99/0.98  
% 2.99/0.98  --schedule                              default
% 2.99/0.98  --add_important_lit                     false
% 2.99/0.98  --prop_solver_per_cl                    1000
% 2.99/0.98  --min_unsat_core                        false
% 2.99/0.98  --soft_assumptions                      false
% 2.99/0.98  --soft_lemma_size                       3
% 2.99/0.98  --prop_impl_unit_size                   0
% 2.99/0.98  --prop_impl_unit                        []
% 2.99/0.98  --share_sel_clauses                     true
% 2.99/0.98  --reset_solvers                         false
% 2.99/0.98  --bc_imp_inh                            [conj_cone]
% 2.99/0.98  --conj_cone_tolerance                   3.
% 2.99/0.98  --extra_neg_conj                        none
% 2.99/0.98  --large_theory_mode                     true
% 2.99/0.98  --prolific_symb_bound                   200
% 2.99/0.98  --lt_threshold                          2000
% 2.99/0.98  --clause_weak_htbl                      true
% 2.99/0.98  --gc_record_bc_elim                     false
% 2.99/0.98  
% 2.99/0.98  ------ Preprocessing Options
% 2.99/0.98  
% 2.99/0.98  --preprocessing_flag                    true
% 2.99/0.98  --time_out_prep_mult                    0.1
% 2.99/0.98  --splitting_mode                        input
% 2.99/0.98  --splitting_grd                         true
% 2.99/0.98  --splitting_cvd                         false
% 2.99/0.98  --splitting_cvd_svl                     false
% 2.99/0.98  --splitting_nvd                         32
% 2.99/0.98  --sub_typing                            true
% 2.99/0.98  --prep_gs_sim                           true
% 2.99/0.98  --prep_unflatten                        true
% 2.99/0.98  --prep_res_sim                          true
% 2.99/0.98  --prep_upred                            true
% 2.99/0.98  --prep_sem_filter                       exhaustive
% 2.99/0.98  --prep_sem_filter_out                   false
% 2.99/0.98  --pred_elim                             true
% 2.99/0.98  --res_sim_input                         true
% 2.99/0.98  --eq_ax_congr_red                       true
% 2.99/0.98  --pure_diseq_elim                       true
% 2.99/0.98  --brand_transform                       false
% 2.99/0.98  --non_eq_to_eq                          false
% 2.99/0.98  --prep_def_merge                        true
% 2.99/0.98  --prep_def_merge_prop_impl              false
% 2.99/0.98  --prep_def_merge_mbd                    true
% 2.99/0.98  --prep_def_merge_tr_red                 false
% 2.99/0.98  --prep_def_merge_tr_cl                  false
% 2.99/0.98  --smt_preprocessing                     true
% 2.99/0.98  --smt_ac_axioms                         fast
% 2.99/0.98  --preprocessed_out                      false
% 2.99/0.98  --preprocessed_stats                    false
% 2.99/0.98  
% 2.99/0.98  ------ Abstraction refinement Options
% 2.99/0.98  
% 2.99/0.98  --abstr_ref                             []
% 2.99/0.98  --abstr_ref_prep                        false
% 2.99/0.98  --abstr_ref_until_sat                   false
% 2.99/0.98  --abstr_ref_sig_restrict                funpre
% 2.99/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/0.98  --abstr_ref_under                       []
% 2.99/0.98  
% 2.99/0.98  ------ SAT Options
% 2.99/0.98  
% 2.99/0.98  --sat_mode                              false
% 2.99/0.98  --sat_fm_restart_options                ""
% 2.99/0.98  --sat_gr_def                            false
% 2.99/0.98  --sat_epr_types                         true
% 2.99/0.98  --sat_non_cyclic_types                  false
% 2.99/0.98  --sat_finite_models                     false
% 2.99/0.98  --sat_fm_lemmas                         false
% 2.99/0.98  --sat_fm_prep                           false
% 2.99/0.98  --sat_fm_uc_incr                        true
% 2.99/0.98  --sat_out_model                         small
% 2.99/0.98  --sat_out_clauses                       false
% 2.99/0.98  
% 2.99/0.98  ------ QBF Options
% 2.99/0.98  
% 2.99/0.98  --qbf_mode                              false
% 2.99/0.98  --qbf_elim_univ                         false
% 2.99/0.98  --qbf_dom_inst                          none
% 2.99/0.98  --qbf_dom_pre_inst                      false
% 2.99/0.98  --qbf_sk_in                             false
% 2.99/0.98  --qbf_pred_elim                         true
% 2.99/0.98  --qbf_split                             512
% 2.99/0.98  
% 2.99/0.98  ------ BMC1 Options
% 2.99/0.98  
% 2.99/0.98  --bmc1_incremental                      false
% 2.99/0.98  --bmc1_axioms                           reachable_all
% 2.99/0.98  --bmc1_min_bound                        0
% 2.99/0.98  --bmc1_max_bound                        -1
% 2.99/0.98  --bmc1_max_bound_default                -1
% 2.99/0.98  --bmc1_symbol_reachability              true
% 2.99/0.98  --bmc1_property_lemmas                  false
% 2.99/0.98  --bmc1_k_induction                      false
% 2.99/0.98  --bmc1_non_equiv_states                 false
% 2.99/0.98  --bmc1_deadlock                         false
% 2.99/0.98  --bmc1_ucm                              false
% 2.99/0.98  --bmc1_add_unsat_core                   none
% 2.99/0.98  --bmc1_unsat_core_children              false
% 2.99/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/0.98  --bmc1_out_stat                         full
% 2.99/0.98  --bmc1_ground_init                      false
% 2.99/0.98  --bmc1_pre_inst_next_state              false
% 2.99/0.98  --bmc1_pre_inst_state                   false
% 2.99/0.98  --bmc1_pre_inst_reach_state             false
% 2.99/0.98  --bmc1_out_unsat_core                   false
% 2.99/0.98  --bmc1_aig_witness_out                  false
% 2.99/0.98  --bmc1_verbose                          false
% 2.99/0.98  --bmc1_dump_clauses_tptp                false
% 2.99/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.99/0.98  --bmc1_dump_file                        -
% 2.99/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.99/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.99/0.98  --bmc1_ucm_extend_mode                  1
% 2.99/0.98  --bmc1_ucm_init_mode                    2
% 2.99/0.98  --bmc1_ucm_cone_mode                    none
% 2.99/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.99/0.98  --bmc1_ucm_relax_model                  4
% 2.99/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.99/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/0.98  --bmc1_ucm_layered_model                none
% 2.99/0.98  --bmc1_ucm_max_lemma_size               10
% 2.99/0.98  
% 2.99/0.98  ------ AIG Options
% 2.99/0.98  
% 2.99/0.98  --aig_mode                              false
% 2.99/0.98  
% 2.99/0.98  ------ Instantiation Options
% 2.99/0.98  
% 2.99/0.98  --instantiation_flag                    true
% 2.99/0.98  --inst_sos_flag                         false
% 2.99/0.98  --inst_sos_phase                        true
% 2.99/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/0.98  --inst_lit_sel_side                     num_symb
% 2.99/0.98  --inst_solver_per_active                1400
% 2.99/0.98  --inst_solver_calls_frac                1.
% 2.99/0.98  --inst_passive_queue_type               priority_queues
% 2.99/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/0.98  --inst_passive_queues_freq              [25;2]
% 2.99/0.98  --inst_dismatching                      true
% 2.99/0.98  --inst_eager_unprocessed_to_passive     true
% 2.99/0.98  --inst_prop_sim_given                   true
% 2.99/0.98  --inst_prop_sim_new                     false
% 2.99/0.98  --inst_subs_new                         false
% 2.99/0.98  --inst_eq_res_simp                      false
% 2.99/0.98  --inst_subs_given                       false
% 2.99/0.98  --inst_orphan_elimination               true
% 2.99/0.98  --inst_learning_loop_flag               true
% 2.99/0.98  --inst_learning_start                   3000
% 2.99/0.98  --inst_learning_factor                  2
% 2.99/0.98  --inst_start_prop_sim_after_learn       3
% 2.99/0.98  --inst_sel_renew                        solver
% 2.99/0.98  --inst_lit_activity_flag                true
% 2.99/0.98  --inst_restr_to_given                   false
% 2.99/0.98  --inst_activity_threshold               500
% 2.99/0.98  --inst_out_proof                        true
% 2.99/0.98  
% 2.99/0.98  ------ Resolution Options
% 2.99/0.98  
% 2.99/0.98  --resolution_flag                       true
% 2.99/0.98  --res_lit_sel                           adaptive
% 2.99/0.98  --res_lit_sel_side                      none
% 2.99/0.98  --res_ordering                          kbo
% 2.99/0.98  --res_to_prop_solver                    active
% 2.99/0.98  --res_prop_simpl_new                    false
% 2.99/0.98  --res_prop_simpl_given                  true
% 2.99/0.98  --res_passive_queue_type                priority_queues
% 2.99/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/0.98  --res_passive_queues_freq               [15;5]
% 2.99/0.98  --res_forward_subs                      full
% 2.99/0.98  --res_backward_subs                     full
% 2.99/0.98  --res_forward_subs_resolution           true
% 2.99/0.98  --res_backward_subs_resolution          true
% 2.99/0.98  --res_orphan_elimination                true
% 2.99/0.98  --res_time_limit                        2.
% 2.99/0.98  --res_out_proof                         true
% 2.99/0.98  
% 2.99/0.98  ------ Superposition Options
% 2.99/0.98  
% 2.99/0.98  --superposition_flag                    true
% 2.99/0.98  --sup_passive_queue_type                priority_queues
% 2.99/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.99/0.98  --demod_completeness_check              fast
% 2.99/0.98  --demod_use_ground                      true
% 2.99/0.98  --sup_to_prop_solver                    passive
% 2.99/0.98  --sup_prop_simpl_new                    true
% 2.99/0.98  --sup_prop_simpl_given                  true
% 2.99/0.98  --sup_fun_splitting                     false
% 2.99/0.98  --sup_smt_interval                      50000
% 2.99/0.98  
% 2.99/0.98  ------ Superposition Simplification Setup
% 2.99/0.98  
% 2.99/0.98  --sup_indices_passive                   []
% 2.99/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.98  --sup_full_bw                           [BwDemod]
% 2.99/0.98  --sup_immed_triv                        [TrivRules]
% 2.99/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.98  --sup_immed_bw_main                     []
% 2.99/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.98  
% 2.99/0.98  ------ Combination Options
% 2.99/0.98  
% 2.99/0.98  --comb_res_mult                         3
% 2.99/0.98  --comb_sup_mult                         2
% 2.99/0.98  --comb_inst_mult                        10
% 2.99/0.98  
% 2.99/0.98  ------ Debug Options
% 2.99/0.98  
% 2.99/0.98  --dbg_backtrace                         false
% 2.99/0.98  --dbg_dump_prop_clauses                 false
% 2.99/0.98  --dbg_dump_prop_clauses_file            -
% 2.99/0.98  --dbg_out_stat                          false
% 2.99/0.98  ------ Parsing...
% 2.99/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.99/0.98  
% 2.99/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.99/0.98  
% 2.99/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.99/0.98  
% 2.99/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.99/0.98  ------ Proving...
% 2.99/0.98  ------ Problem Properties 
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  clauses                                 27
% 2.99/0.98  conjectures                             11
% 2.99/0.98  EPR                                     11
% 2.99/0.98  Horn                                    26
% 2.99/0.98  unary                                   12
% 2.99/0.98  binary                                  4
% 2.99/0.98  lits                                    73
% 2.99/0.98  lits eq                                 7
% 2.99/0.98  fd_pure                                 0
% 2.99/0.98  fd_pseudo                               0
% 2.99/0.98  fd_cond                                 0
% 2.99/0.98  fd_pseudo_cond                          1
% 2.99/0.98  AC symbols                              0
% 2.99/0.98  
% 2.99/0.98  ------ Schedule dynamic 5 is on 
% 2.99/0.98  
% 2.99/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  ------ 
% 2.99/0.98  Current options:
% 2.99/0.98  ------ 
% 2.99/0.98  
% 2.99/0.98  ------ Input Options
% 2.99/0.98  
% 2.99/0.98  --out_options                           all
% 2.99/0.98  --tptp_safe_out                         true
% 2.99/0.98  --problem_path                          ""
% 2.99/0.98  --include_path                          ""
% 2.99/0.98  --clausifier                            res/vclausify_rel
% 2.99/0.98  --clausifier_options                    --mode clausify
% 2.99/0.98  --stdin                                 false
% 2.99/0.98  --stats_out                             all
% 2.99/0.98  
% 2.99/0.98  ------ General Options
% 2.99/0.98  
% 2.99/0.98  --fof                                   false
% 2.99/0.98  --time_out_real                         305.
% 2.99/0.98  --time_out_virtual                      -1.
% 2.99/0.98  --symbol_type_check                     false
% 2.99/0.98  --clausify_out                          false
% 2.99/0.98  --sig_cnt_out                           false
% 2.99/0.98  --trig_cnt_out                          false
% 2.99/0.98  --trig_cnt_out_tolerance                1.
% 2.99/0.98  --trig_cnt_out_sk_spl                   false
% 2.99/0.98  --abstr_cl_out                          false
% 2.99/0.98  
% 2.99/0.98  ------ Global Options
% 2.99/0.98  
% 2.99/0.98  --schedule                              default
% 2.99/0.98  --add_important_lit                     false
% 2.99/0.98  --prop_solver_per_cl                    1000
% 2.99/0.98  --min_unsat_core                        false
% 2.99/0.98  --soft_assumptions                      false
% 2.99/0.98  --soft_lemma_size                       3
% 2.99/0.98  --prop_impl_unit_size                   0
% 2.99/0.98  --prop_impl_unit                        []
% 2.99/0.98  --share_sel_clauses                     true
% 2.99/0.98  --reset_solvers                         false
% 2.99/0.98  --bc_imp_inh                            [conj_cone]
% 2.99/0.98  --conj_cone_tolerance                   3.
% 2.99/0.98  --extra_neg_conj                        none
% 2.99/0.98  --large_theory_mode                     true
% 2.99/0.98  --prolific_symb_bound                   200
% 2.99/0.98  --lt_threshold                          2000
% 2.99/0.98  --clause_weak_htbl                      true
% 2.99/0.98  --gc_record_bc_elim                     false
% 2.99/0.98  
% 2.99/0.98  ------ Preprocessing Options
% 2.99/0.98  
% 2.99/0.98  --preprocessing_flag                    true
% 2.99/0.98  --time_out_prep_mult                    0.1
% 2.99/0.98  --splitting_mode                        input
% 2.99/0.98  --splitting_grd                         true
% 2.99/0.98  --splitting_cvd                         false
% 2.99/0.98  --splitting_cvd_svl                     false
% 2.99/0.98  --splitting_nvd                         32
% 2.99/0.98  --sub_typing                            true
% 2.99/0.98  --prep_gs_sim                           true
% 2.99/0.98  --prep_unflatten                        true
% 2.99/0.98  --prep_res_sim                          true
% 2.99/0.98  --prep_upred                            true
% 2.99/0.98  --prep_sem_filter                       exhaustive
% 2.99/0.98  --prep_sem_filter_out                   false
% 2.99/0.98  --pred_elim                             true
% 2.99/0.98  --res_sim_input                         true
% 2.99/0.98  --eq_ax_congr_red                       true
% 2.99/0.98  --pure_diseq_elim                       true
% 2.99/0.98  --brand_transform                       false
% 2.99/0.98  --non_eq_to_eq                          false
% 2.99/0.98  --prep_def_merge                        true
% 2.99/0.98  --prep_def_merge_prop_impl              false
% 2.99/0.98  --prep_def_merge_mbd                    true
% 2.99/0.98  --prep_def_merge_tr_red                 false
% 2.99/0.98  --prep_def_merge_tr_cl                  false
% 2.99/0.98  --smt_preprocessing                     true
% 2.99/0.98  --smt_ac_axioms                         fast
% 2.99/0.98  --preprocessed_out                      false
% 2.99/0.98  --preprocessed_stats                    false
% 2.99/0.98  
% 2.99/0.98  ------ Abstraction refinement Options
% 2.99/0.98  
% 2.99/0.98  --abstr_ref                             []
% 2.99/0.98  --abstr_ref_prep                        false
% 2.99/0.98  --abstr_ref_until_sat                   false
% 2.99/0.98  --abstr_ref_sig_restrict                funpre
% 2.99/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/0.98  --abstr_ref_under                       []
% 2.99/0.98  
% 2.99/0.98  ------ SAT Options
% 2.99/0.98  
% 2.99/0.98  --sat_mode                              false
% 2.99/0.98  --sat_fm_restart_options                ""
% 2.99/0.98  --sat_gr_def                            false
% 2.99/0.98  --sat_epr_types                         true
% 2.99/0.98  --sat_non_cyclic_types                  false
% 2.99/0.98  --sat_finite_models                     false
% 2.99/0.98  --sat_fm_lemmas                         false
% 2.99/0.98  --sat_fm_prep                           false
% 2.99/0.98  --sat_fm_uc_incr                        true
% 2.99/0.98  --sat_out_model                         small
% 2.99/0.98  --sat_out_clauses                       false
% 2.99/0.98  
% 2.99/0.98  ------ QBF Options
% 2.99/0.98  
% 2.99/0.98  --qbf_mode                              false
% 2.99/0.98  --qbf_elim_univ                         false
% 2.99/0.98  --qbf_dom_inst                          none
% 2.99/0.98  --qbf_dom_pre_inst                      false
% 2.99/0.98  --qbf_sk_in                             false
% 2.99/0.98  --qbf_pred_elim                         true
% 2.99/0.98  --qbf_split                             512
% 2.99/0.98  
% 2.99/0.98  ------ BMC1 Options
% 2.99/0.98  
% 2.99/0.98  --bmc1_incremental                      false
% 2.99/0.98  --bmc1_axioms                           reachable_all
% 2.99/0.98  --bmc1_min_bound                        0
% 2.99/0.98  --bmc1_max_bound                        -1
% 2.99/0.98  --bmc1_max_bound_default                -1
% 2.99/0.98  --bmc1_symbol_reachability              true
% 2.99/0.98  --bmc1_property_lemmas                  false
% 2.99/0.98  --bmc1_k_induction                      false
% 2.99/0.98  --bmc1_non_equiv_states                 false
% 2.99/0.98  --bmc1_deadlock                         false
% 2.99/0.98  --bmc1_ucm                              false
% 2.99/0.98  --bmc1_add_unsat_core                   none
% 2.99/0.98  --bmc1_unsat_core_children              false
% 2.99/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/0.98  --bmc1_out_stat                         full
% 2.99/0.98  --bmc1_ground_init                      false
% 2.99/0.98  --bmc1_pre_inst_next_state              false
% 2.99/0.98  --bmc1_pre_inst_state                   false
% 2.99/0.98  --bmc1_pre_inst_reach_state             false
% 2.99/0.98  --bmc1_out_unsat_core                   false
% 2.99/0.98  --bmc1_aig_witness_out                  false
% 2.99/0.98  --bmc1_verbose                          false
% 2.99/0.98  --bmc1_dump_clauses_tptp                false
% 2.99/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.99/0.98  --bmc1_dump_file                        -
% 2.99/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.99/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.99/0.98  --bmc1_ucm_extend_mode                  1
% 2.99/0.98  --bmc1_ucm_init_mode                    2
% 2.99/0.98  --bmc1_ucm_cone_mode                    none
% 2.99/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.99/0.98  --bmc1_ucm_relax_model                  4
% 2.99/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.99/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/0.98  --bmc1_ucm_layered_model                none
% 2.99/0.98  --bmc1_ucm_max_lemma_size               10
% 2.99/0.98  
% 2.99/0.98  ------ AIG Options
% 2.99/0.98  
% 2.99/0.98  --aig_mode                              false
% 2.99/0.98  
% 2.99/0.98  ------ Instantiation Options
% 2.99/0.98  
% 2.99/0.98  --instantiation_flag                    true
% 2.99/0.98  --inst_sos_flag                         false
% 2.99/0.98  --inst_sos_phase                        true
% 2.99/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/0.98  --inst_lit_sel_side                     none
% 2.99/0.98  --inst_solver_per_active                1400
% 2.99/0.98  --inst_solver_calls_frac                1.
% 2.99/0.98  --inst_passive_queue_type               priority_queues
% 2.99/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/0.98  --inst_passive_queues_freq              [25;2]
% 2.99/0.98  --inst_dismatching                      true
% 2.99/0.98  --inst_eager_unprocessed_to_passive     true
% 2.99/0.98  --inst_prop_sim_given                   true
% 2.99/0.98  --inst_prop_sim_new                     false
% 2.99/0.98  --inst_subs_new                         false
% 2.99/0.98  --inst_eq_res_simp                      false
% 2.99/0.98  --inst_subs_given                       false
% 2.99/0.98  --inst_orphan_elimination               true
% 2.99/0.98  --inst_learning_loop_flag               true
% 2.99/0.98  --inst_learning_start                   3000
% 2.99/0.98  --inst_learning_factor                  2
% 2.99/0.98  --inst_start_prop_sim_after_learn       3
% 2.99/0.98  --inst_sel_renew                        solver
% 2.99/0.98  --inst_lit_activity_flag                true
% 2.99/0.98  --inst_restr_to_given                   false
% 2.99/0.98  --inst_activity_threshold               500
% 2.99/0.98  --inst_out_proof                        true
% 2.99/0.98  
% 2.99/0.98  ------ Resolution Options
% 2.99/0.98  
% 2.99/0.98  --resolution_flag                       false
% 2.99/0.98  --res_lit_sel                           adaptive
% 2.99/0.98  --res_lit_sel_side                      none
% 2.99/0.98  --res_ordering                          kbo
% 2.99/0.98  --res_to_prop_solver                    active
% 2.99/0.98  --res_prop_simpl_new                    false
% 2.99/0.98  --res_prop_simpl_given                  true
% 2.99/0.98  --res_passive_queue_type                priority_queues
% 2.99/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/0.98  --res_passive_queues_freq               [15;5]
% 2.99/0.98  --res_forward_subs                      full
% 2.99/0.98  --res_backward_subs                     full
% 2.99/0.98  --res_forward_subs_resolution           true
% 2.99/0.98  --res_backward_subs_resolution          true
% 2.99/0.98  --res_orphan_elimination                true
% 2.99/0.98  --res_time_limit                        2.
% 2.99/0.98  --res_out_proof                         true
% 2.99/0.98  
% 2.99/0.98  ------ Superposition Options
% 2.99/0.98  
% 2.99/0.98  --superposition_flag                    true
% 2.99/0.98  --sup_passive_queue_type                priority_queues
% 2.99/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.99/0.98  --demod_completeness_check              fast
% 2.99/0.98  --demod_use_ground                      true
% 2.99/0.98  --sup_to_prop_solver                    passive
% 2.99/0.98  --sup_prop_simpl_new                    true
% 2.99/0.98  --sup_prop_simpl_given                  true
% 2.99/0.98  --sup_fun_splitting                     false
% 2.99/0.98  --sup_smt_interval                      50000
% 2.99/0.98  
% 2.99/0.98  ------ Superposition Simplification Setup
% 2.99/0.98  
% 2.99/0.98  --sup_indices_passive                   []
% 2.99/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.98  --sup_full_bw                           [BwDemod]
% 2.99/0.98  --sup_immed_triv                        [TrivRules]
% 2.99/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.98  --sup_immed_bw_main                     []
% 2.99/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.98  
% 2.99/0.98  ------ Combination Options
% 2.99/0.98  
% 2.99/0.98  --comb_res_mult                         3
% 2.99/0.98  --comb_sup_mult                         2
% 2.99/0.98  --comb_inst_mult                        10
% 2.99/0.98  
% 2.99/0.98  ------ Debug Options
% 2.99/0.98  
% 2.99/0.98  --dbg_backtrace                         false
% 2.99/0.98  --dbg_dump_prop_clauses                 false
% 2.99/0.98  --dbg_dump_prop_clauses_file            -
% 2.99/0.98  --dbg_out_stat                          false
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  ------ Proving...
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  % SZS status Theorem for theBenchmark.p
% 2.99/0.98  
% 2.99/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.99/0.98  
% 2.99/0.98  fof(f17,conjecture,(
% 2.99/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 2.99/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f18,negated_conjecture,(
% 2.99/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 2.99/0.98    inference(negated_conjecture,[],[f17])).
% 2.99/0.98  
% 2.99/0.98  fof(f44,plain,(
% 2.99/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.99/0.98    inference(ennf_transformation,[],[f18])).
% 2.99/0.98  
% 2.99/0.98  fof(f45,plain,(
% 2.99/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.99/0.98    inference(flattening,[],[f44])).
% 2.99/0.98  
% 2.99/0.98  fof(f55,plain,(
% 2.99/0.98    ( ! [X2,X0,X1] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 2.99/0.98    introduced(choice_axiom,[])).
% 2.99/0.98  
% 2.99/0.98  fof(f54,plain,(
% 2.99/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 2.99/0.98    introduced(choice_axiom,[])).
% 2.99/0.98  
% 2.99/0.98  fof(f53,plain,(
% 2.99/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.99/0.98    introduced(choice_axiom,[])).
% 2.99/0.98  
% 2.99/0.98  fof(f52,plain,(
% 2.99/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.99/0.98    introduced(choice_axiom,[])).
% 2.99/0.98  
% 2.99/0.98  fof(f56,plain,(
% 2.99/0.98    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.99/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f45,f55,f54,f53,f52])).
% 2.99/0.98  
% 2.99/0.98  fof(f86,plain,(
% 2.99/0.98    m1_pre_topc(sK2,sK1)),
% 2.99/0.98    inference(cnf_transformation,[],[f56])).
% 2.99/0.98  
% 2.99/0.98  fof(f90,plain,(
% 2.99/0.98    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 2.99/0.98    inference(cnf_transformation,[],[f56])).
% 2.99/0.98  
% 2.99/0.98  fof(f13,axiom,(
% 2.99/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.99/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f20,plain,(
% 2.99/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 2.99/0.98    inference(pure_predicate_removal,[],[f13])).
% 2.99/0.98  
% 2.99/0.98  fof(f38,plain,(
% 2.99/0.98    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.99/0.98    inference(ennf_transformation,[],[f20])).
% 2.99/0.98  
% 2.99/0.98  fof(f73,plain,(
% 2.99/0.98    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f38])).
% 2.99/0.98  
% 2.99/0.98  fof(f14,axiom,(
% 2.99/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 2.99/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f39,plain,(
% 2.99/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 2.99/0.98    inference(ennf_transformation,[],[f14])).
% 2.99/0.98  
% 2.99/0.98  fof(f40,plain,(
% 2.99/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.99/0.98    inference(flattening,[],[f39])).
% 2.99/0.98  
% 2.99/0.98  fof(f50,plain,(
% 2.99/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.99/0.98    inference(nnf_transformation,[],[f40])).
% 2.99/0.98  
% 2.99/0.98  fof(f74,plain,(
% 2.99/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f50])).
% 2.99/0.98  
% 2.99/0.98  fof(f96,plain,(
% 2.99/0.98    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 2.99/0.98    inference(equality_resolution,[],[f74])).
% 2.99/0.98  
% 2.99/0.98  fof(f10,axiom,(
% 2.99/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.99/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f19,plain,(
% 2.99/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 2.99/0.98    inference(pure_predicate_removal,[],[f10])).
% 2.99/0.98  
% 2.99/0.98  fof(f32,plain,(
% 2.99/0.98    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.99/0.98    inference(ennf_transformation,[],[f19])).
% 2.99/0.98  
% 2.99/0.98  fof(f33,plain,(
% 2.99/0.98    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.99/0.98    inference(flattening,[],[f32])).
% 2.99/0.98  
% 2.99/0.98  fof(f69,plain,(
% 2.99/0.98    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f33])).
% 2.99/0.98  
% 2.99/0.98  fof(f8,axiom,(
% 2.99/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.99/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f29,plain,(
% 2.99/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.99/0.98    inference(ennf_transformation,[],[f8])).
% 2.99/0.98  
% 2.99/0.98  fof(f67,plain,(
% 2.99/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f29])).
% 2.99/0.98  
% 2.99/0.98  fof(f83,plain,(
% 2.99/0.98    v2_pre_topc(sK1)),
% 2.99/0.98    inference(cnf_transformation,[],[f56])).
% 2.99/0.98  
% 2.99/0.98  fof(f84,plain,(
% 2.99/0.98    l1_pre_topc(sK1)),
% 2.99/0.98    inference(cnf_transformation,[],[f56])).
% 2.99/0.98  
% 2.99/0.98  fof(f1,axiom,(
% 2.99/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.99/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f46,plain,(
% 2.99/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.99/0.98    inference(nnf_transformation,[],[f1])).
% 2.99/0.98  
% 2.99/0.98  fof(f47,plain,(
% 2.99/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.99/0.98    inference(flattening,[],[f46])).
% 2.99/0.98  
% 2.99/0.98  fof(f57,plain,(
% 2.99/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.99/0.98    inference(cnf_transformation,[],[f47])).
% 2.99/0.98  
% 2.99/0.98  fof(f93,plain,(
% 2.99/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.99/0.98    inference(equality_resolution,[],[f57])).
% 2.99/0.98  
% 2.99/0.98  fof(f59,plain,(
% 2.99/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f47])).
% 2.99/0.98  
% 2.99/0.98  fof(f16,axiom,(
% 2.99/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 2.99/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f42,plain,(
% 2.99/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.99/0.98    inference(ennf_transformation,[],[f16])).
% 2.99/0.98  
% 2.99/0.98  fof(f43,plain,(
% 2.99/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.99/0.98    inference(flattening,[],[f42])).
% 2.99/0.98  
% 2.99/0.98  fof(f51,plain,(
% 2.99/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.99/0.98    inference(nnf_transformation,[],[f43])).
% 2.99/0.98  
% 2.99/0.98  fof(f78,plain,(
% 2.99/0.98    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f51])).
% 2.99/0.98  
% 2.99/0.98  fof(f15,axiom,(
% 2.99/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.99/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f41,plain,(
% 2.99/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.99/0.98    inference(ennf_transformation,[],[f15])).
% 2.99/0.98  
% 2.99/0.98  fof(f76,plain,(
% 2.99/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f41])).
% 2.99/0.98  
% 2.99/0.98  fof(f2,axiom,(
% 2.99/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.99/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f48,plain,(
% 2.99/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.99/0.98    inference(nnf_transformation,[],[f2])).
% 2.99/0.98  
% 2.99/0.98  fof(f60,plain,(
% 2.99/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.99/0.98    inference(cnf_transformation,[],[f48])).
% 2.99/0.98  
% 2.99/0.98  fof(f58,plain,(
% 2.99/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.99/0.98    inference(cnf_transformation,[],[f47])).
% 2.99/0.98  
% 2.99/0.98  fof(f92,plain,(
% 2.99/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.99/0.98    inference(equality_resolution,[],[f58])).
% 2.99/0.98  
% 2.99/0.98  fof(f77,plain,(
% 2.99/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f51])).
% 2.99/0.98  
% 2.99/0.98  fof(f89,plain,(
% 2.99/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.99/0.98    inference(cnf_transformation,[],[f56])).
% 2.99/0.98  
% 2.99/0.98  fof(f12,axiom,(
% 2.99/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 2.99/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f36,plain,(
% 2.99/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.99/0.98    inference(ennf_transformation,[],[f12])).
% 2.99/0.98  
% 2.99/0.98  fof(f37,plain,(
% 2.99/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.99/0.98    inference(flattening,[],[f36])).
% 2.99/0.98  
% 2.99/0.98  fof(f72,plain,(
% 2.99/0.98    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f37])).
% 2.99/0.98  
% 2.99/0.98  fof(f87,plain,(
% 2.99/0.98    v1_funct_1(sK3)),
% 2.99/0.98    inference(cnf_transformation,[],[f56])).
% 2.99/0.98  
% 2.99/0.98  fof(f6,axiom,(
% 2.99/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 2.99/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f26,plain,(
% 2.99/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.99/0.98    inference(ennf_transformation,[],[f6])).
% 2.99/0.98  
% 2.99/0.98  fof(f27,plain,(
% 2.99/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.99/0.98    inference(flattening,[],[f26])).
% 2.99/0.98  
% 2.99/0.98  fof(f65,plain,(
% 2.99/0.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f27])).
% 2.99/0.98  
% 2.99/0.98  fof(f79,plain,(
% 2.99/0.98    ~v2_struct_0(sK0)),
% 2.99/0.98    inference(cnf_transformation,[],[f56])).
% 2.99/0.98  
% 2.99/0.98  fof(f80,plain,(
% 2.99/0.98    v2_pre_topc(sK0)),
% 2.99/0.98    inference(cnf_transformation,[],[f56])).
% 2.99/0.98  
% 2.99/0.98  fof(f81,plain,(
% 2.99/0.98    l1_pre_topc(sK0)),
% 2.99/0.98    inference(cnf_transformation,[],[f56])).
% 2.99/0.98  
% 2.99/0.98  fof(f82,plain,(
% 2.99/0.98    ~v2_struct_0(sK1)),
% 2.99/0.98    inference(cnf_transformation,[],[f56])).
% 2.99/0.98  
% 2.99/0.98  fof(f88,plain,(
% 2.99/0.98    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.99/0.98    inference(cnf_transformation,[],[f56])).
% 2.99/0.98  
% 2.99/0.98  fof(f7,axiom,(
% 2.99/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.99/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f28,plain,(
% 2.99/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.99/0.98    inference(ennf_transformation,[],[f7])).
% 2.99/0.98  
% 2.99/0.98  fof(f66,plain,(
% 2.99/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f28])).
% 2.99/0.98  
% 2.99/0.98  fof(f9,axiom,(
% 2.99/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.99/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f30,plain,(
% 2.99/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.99/0.98    inference(ennf_transformation,[],[f9])).
% 2.99/0.98  
% 2.99/0.98  fof(f31,plain,(
% 2.99/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.99/0.98    inference(flattening,[],[f30])).
% 2.99/0.98  
% 2.99/0.98  fof(f68,plain,(
% 2.99/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f31])).
% 2.99/0.98  
% 2.99/0.98  fof(f11,axiom,(
% 2.99/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 2.99/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f34,plain,(
% 2.99/0.98    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.99/0.98    inference(ennf_transformation,[],[f11])).
% 2.99/0.98  
% 2.99/0.98  fof(f35,plain,(
% 2.99/0.98    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.99/0.98    inference(flattening,[],[f34])).
% 2.99/0.98  
% 2.99/0.98  fof(f49,plain,(
% 2.99/0.98    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.99/0.98    inference(nnf_transformation,[],[f35])).
% 2.99/0.98  
% 2.99/0.98  fof(f71,plain,(
% 2.99/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f49])).
% 2.99/0.98  
% 2.99/0.98  fof(f94,plain,(
% 2.99/0.98    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.99/0.98    inference(equality_resolution,[],[f71])).
% 2.99/0.98  
% 2.99/0.98  fof(f91,plain,(
% 2.99/0.98    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 2.99/0.98    inference(cnf_transformation,[],[f56])).
% 2.99/0.98  
% 2.99/0.98  fof(f5,axiom,(
% 2.99/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.99/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f21,plain,(
% 2.99/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.99/0.98    inference(pure_predicate_removal,[],[f5])).
% 2.99/0.98  
% 2.99/0.98  fof(f25,plain,(
% 2.99/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/0.98    inference(ennf_transformation,[],[f21])).
% 2.99/0.98  
% 2.99/0.98  fof(f64,plain,(
% 2.99/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/0.98    inference(cnf_transformation,[],[f25])).
% 2.99/0.98  
% 2.99/0.98  fof(f3,axiom,(
% 2.99/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.99/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f22,plain,(
% 2.99/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.99/0.98    inference(ennf_transformation,[],[f3])).
% 2.99/0.98  
% 2.99/0.98  fof(f23,plain,(
% 2.99/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.99/0.98    inference(flattening,[],[f22])).
% 2.99/0.98  
% 2.99/0.98  fof(f62,plain,(
% 2.99/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f23])).
% 2.99/0.98  
% 2.99/0.98  fof(f4,axiom,(
% 2.99/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.99/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f24,plain,(
% 2.99/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/0.98    inference(ennf_transformation,[],[f4])).
% 2.99/0.98  
% 2.99/0.98  fof(f63,plain,(
% 2.99/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/0.98    inference(cnf_transformation,[],[f24])).
% 2.99/0.98  
% 2.99/0.98  cnf(c_27,negated_conjecture,
% 2.99/0.98      ( m1_pre_topc(sK2,sK1) ),
% 2.99/0.98      inference(cnf_transformation,[],[f86]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1586,plain,
% 2.99/0.98      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_23,negated_conjecture,
% 2.99/0.98      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 2.99/0.98      inference(cnf_transformation,[],[f90]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_16,plain,
% 2.99/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.99/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 2.99/0.98      | ~ l1_pre_topc(X1) ),
% 2.99/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1592,plain,
% 2.99/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 2.99/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 2.99/0.98      | l1_pre_topc(X1) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3148,plain,
% 2.99/0.98      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top
% 2.99/0.98      | m1_pre_topc(sK2,X0) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_23,c_1592]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_18,plain,
% 2.99/0.98      ( m1_pre_topc(X0,X1)
% 2.99/0.98      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 2.99/0.98      | ~ v2_pre_topc(X0)
% 2.99/0.98      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 2.99/0.98      | ~ l1_pre_topc(X1)
% 2.99/0.98      | ~ l1_pre_topc(X0)
% 2.99/0.98      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.99/0.98      inference(cnf_transformation,[],[f96]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_12,plain,
% 2.99/0.98      ( ~ v2_pre_topc(X0)
% 2.99/0.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 2.99/0.98      | ~ l1_pre_topc(X0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_191,plain,
% 2.99/0.98      ( ~ v2_pre_topc(X0)
% 2.99/0.98      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 2.99/0.98      | m1_pre_topc(X0,X1)
% 2.99/0.98      | ~ l1_pre_topc(X1)
% 2.99/0.98      | ~ l1_pre_topc(X0)
% 2.99/0.98      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_18,c_12]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_192,plain,
% 2.99/0.98      ( m1_pre_topc(X0,X1)
% 2.99/0.98      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 2.99/0.98      | ~ v2_pre_topc(X0)
% 2.99/0.98      | ~ l1_pre_topc(X0)
% 2.99/0.98      | ~ l1_pre_topc(X1)
% 2.99/0.98      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.99/0.98      inference(renaming,[status(thm)],[c_191]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1578,plain,
% 2.99/0.98      ( m1_pre_topc(X0,X1) = iProver_top
% 2.99/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 2.99/0.98      | v2_pre_topc(X0) != iProver_top
% 2.99/0.98      | l1_pre_topc(X1) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0) != iProver_top
% 2.99/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_192]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_10,plain,
% 2.99/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1594,plain,
% 2.99/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 2.99/0.98      | l1_pre_topc(X1) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1707,plain,
% 2.99/0.98      ( m1_pre_topc(X0,X1) = iProver_top
% 2.99/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 2.99/0.98      | v2_pre_topc(X0) != iProver_top
% 2.99/0.98      | l1_pre_topc(X1) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0) != iProver_top ),
% 2.99/0.98      inference(forward_subsumption_resolution,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_1578,c_1594]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4387,plain,
% 2.99/0.98      ( m1_pre_topc(sK2,X0) != iProver_top
% 2.99/0.98      | m1_pre_topc(sK1,X0) = iProver_top
% 2.99/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_3148,c_1707]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_30,negated_conjecture,
% 2.99/0.98      ( v2_pre_topc(sK1) ),
% 2.99/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_39,plain,
% 2.99/0.98      ( v2_pre_topc(sK1) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_29,negated_conjecture,
% 2.99/0.98      ( l1_pre_topc(sK1) ),
% 2.99/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_40,plain,
% 2.99/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4880,plain,
% 2.99/0.98      ( l1_pre_topc(X0) != iProver_top
% 2.99/0.98      | m1_pre_topc(sK2,X0) != iProver_top
% 2.99/0.98      | m1_pre_topc(sK1,X0) = iProver_top ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_4387,c_39,c_40]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4881,plain,
% 2.99/0.98      ( m1_pre_topc(sK2,X0) != iProver_top
% 2.99/0.98      | m1_pre_topc(sK1,X0) = iProver_top
% 2.99/0.98      | l1_pre_topc(X0) != iProver_top ),
% 2.99/0.98      inference(renaming,[status(thm)],[c_4880]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4889,plain,
% 2.99/0.98      ( m1_pre_topc(sK1,sK1) = iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_1586,c_4881]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_42,plain,
% 2.99/0.98      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_54,plain,
% 2.99/0.98      ( m1_pre_topc(X0,X1) = iProver_top
% 2.99/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 2.99/0.98      | v2_pre_topc(X0) != iProver_top
% 2.99/0.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 2.99/0.98      | l1_pre_topc(X1) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0) != iProver_top
% 2.99/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_56,plain,
% 2.99/0.98      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
% 2.99/0.98      | m1_pre_topc(sK1,sK1) = iProver_top
% 2.99/0.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.99/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.99/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_54]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_72,plain,
% 2.99/0.98      ( v2_pre_topc(X0) != iProver_top
% 2.99/0.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 2.99/0.98      | l1_pre_topc(X0) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_74,plain,
% 2.99/0.98      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.99/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_72]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2,plain,
% 2.99/0.98      ( r1_tarski(X0,X0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f93]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_101,plain,
% 2.99/0.98      ( r1_tarski(sK1,sK1) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_0,plain,
% 2.99/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.99/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_105,plain,
% 2.99/0.98      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1834,plain,
% 2.99/0.98      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
% 2.99/0.98      | ~ m1_pre_topc(sK2,sK1)
% 2.99/0.98      | ~ l1_pre_topc(sK1) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1835,plain,
% 2.99/0.98      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) = iProver_top
% 2.99/0.98      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_1834]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1874,plain,
% 2.99/0.98      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 2.99/0.98      | ~ l1_pre_topc(X1)
% 2.99/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1875,plain,
% 2.99/0.98      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 2.99/0.98      | l1_pre_topc(X1) != iProver_top
% 2.99/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_1874]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1877,plain,
% 2.99/0.98      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
% 2.99/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_1875]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_904,plain,
% 2.99/0.98      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.99/0.98      theory(equality) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1892,plain,
% 2.99/0.98      ( m1_pre_topc(X0,X1)
% 2.99/0.98      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
% 2.99/0.98      | X0 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 2.99/0.98      | X1 != sK1 ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_904]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2147,plain,
% 2.99/0.98      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
% 2.99/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
% 2.99/0.98      | X0 != sK1
% 2.99/0.98      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_1892]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2148,plain,
% 2.99/0.98      ( X0 != sK1
% 2.99/0.98      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 2.99/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
% 2.99/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_2147]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2150,plain,
% 2.99/0.98      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 2.99/0.98      | sK1 != sK1
% 2.99/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
% 2.99/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_2148]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4966,plain,
% 2.99/0.98      ( m1_pre_topc(sK1,sK1) = iProver_top ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_4889,c_39,c_40,c_42,c_23,c_56,c_74,c_101,c_105,c_1835,
% 2.99/0.98                 c_1877,c_2150]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_20,plain,
% 2.99/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.99/0.98      | ~ m1_pre_topc(X2,X1)
% 2.99/0.98      | ~ m1_pre_topc(X0,X2)
% 2.99/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 2.99/0.98      | ~ v2_pre_topc(X1)
% 2.99/0.98      | ~ l1_pre_topc(X1) ),
% 2.99/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1590,plain,
% 2.99/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 2.99/0.98      | m1_pre_topc(X2,X1) != iProver_top
% 2.99/0.98      | m1_pre_topc(X0,X2) != iProver_top
% 2.99/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 2.99/0.98      | v2_pre_topc(X1) != iProver_top
% 2.99/0.98      | l1_pre_topc(X1) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4975,plain,
% 2.99/0.98      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.99/0.98      | m1_pre_topc(sK1,X0) != iProver_top
% 2.99/0.98      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
% 2.99/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_4966,c_1590]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_5641,plain,
% 2.99/0.98      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.99/0.98      | m1_pre_topc(sK1,X0) != iProver_top
% 2.99/0.98      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_4975,c_39,c_40]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1598,plain,
% 2.99/0.98      ( X0 = X1
% 2.99/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.99/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_5650,plain,
% 2.99/0.98      ( u1_struct_0(X0) = u1_struct_0(sK1)
% 2.99/0.98      | m1_pre_topc(X0,sK1) != iProver_top
% 2.99/0.98      | m1_pre_topc(sK1,X0) != iProver_top
% 2.99/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_5641,c_1598]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_19,plain,
% 2.99/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.99/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.99/0.98      | ~ l1_pre_topc(X1) ),
% 2.99/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1591,plain,
% 2.99/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 2.99/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 2.99/0.98      | l1_pre_topc(X1) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4,plain,
% 2.99/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.99/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1595,plain,
% 2.99/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.99/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3140,plain,
% 2.99/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 2.99/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 2.99/0.98      | l1_pre_topc(X1) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_1591,c_1595]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3714,plain,
% 2.99/0.98      ( u1_struct_0(X0) = u1_struct_0(X1)
% 2.99/0.98      | m1_pre_topc(X1,X0) != iProver_top
% 2.99/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_3140,c_1598]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_5652,plain,
% 2.99/0.98      ( u1_struct_0(X0) = u1_struct_0(sK1)
% 2.99/0.98      | m1_pre_topc(X0,sK1) != iProver_top
% 2.99/0.98      | m1_pre_topc(sK1,X0) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_5641,c_3714]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_7524,plain,
% 2.99/0.98      ( m1_pre_topc(sK1,X0) != iProver_top
% 2.99/0.98      | m1_pre_topc(X0,sK1) != iProver_top
% 2.99/0.98      | u1_struct_0(X0) = u1_struct_0(sK1) ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_5650,c_40,c_5652]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_7525,plain,
% 2.99/0.98      ( u1_struct_0(X0) = u1_struct_0(sK1)
% 2.99/0.98      | m1_pre_topc(X0,sK1) != iProver_top
% 2.99/0.98      | m1_pre_topc(sK1,X0) != iProver_top ),
% 2.99/0.98      inference(renaming,[status(thm)],[c_7524]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_7532,plain,
% 2.99/0.98      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 2.99/0.98      | m1_pre_topc(sK1,sK2) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_1586,c_7525]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1862,plain,
% 2.99/0.98      ( ~ m1_pre_topc(X0,sK1)
% 2.99/0.98      | ~ m1_pre_topc(sK2,X0)
% 2.99/0.98      | ~ m1_pre_topc(sK2,sK1)
% 2.99/0.98      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 2.99/0.98      | ~ v2_pre_topc(sK1)
% 2.99/0.98      | ~ l1_pre_topc(sK1) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1863,plain,
% 2.99/0.98      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.99/0.98      | m1_pre_topc(sK2,X0) != iProver_top
% 2.99/0.98      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.99/0.98      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 2.99/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_1862]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1865,plain,
% 2.99/0.98      ( m1_pre_topc(sK2,sK1) != iProver_top
% 2.99/0.98      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.99/0.98      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 2.99/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_1863]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2639,plain,
% 2.99/0.98      ( l1_pre_topc(sK2) = iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_1586,c_1594]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3546,plain,
% 2.99/0.98      ( ~ r1_tarski(X0,u1_struct_0(sK2))
% 2.99/0.98      | ~ r1_tarski(u1_struct_0(sK2),X0)
% 2.99/0.98      | u1_struct_0(sK2) = X0 ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4487,plain,
% 2.99/0.98      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
% 2.99/0.98      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 2.99/0.98      | u1_struct_0(sK2) = u1_struct_0(X0) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_3546]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4489,plain,
% 2.99/0.98      ( u1_struct_0(sK2) = u1_struct_0(X0)
% 2.99/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) != iProver_top
% 2.99/0.98      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_4487]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4491,plain,
% 2.99/0.98      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 2.99/0.98      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.99/0.98      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_4489]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4488,plain,
% 2.99/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.99/0.98      | ~ m1_pre_topc(X0,sK2)
% 2.99/0.98      | ~ m1_pre_topc(sK2,X1)
% 2.99/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
% 2.99/0.98      | ~ v2_pre_topc(X1)
% 2.99/0.98      | ~ l1_pre_topc(X1) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4493,plain,
% 2.99/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 2.99/0.98      | m1_pre_topc(X0,sK2) != iProver_top
% 2.99/0.98      | m1_pre_topc(sK2,X1) != iProver_top
% 2.99/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top
% 2.99/0.98      | v2_pre_topc(X1) != iProver_top
% 2.99/0.98      | l1_pre_topc(X1) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_4488]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4495,plain,
% 2.99/0.98      ( m1_pre_topc(sK2,sK1) != iProver_top
% 2.99/0.98      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.99/0.98      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.99/0.98      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top
% 2.99/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_4493]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1,plain,
% 2.99/0.98      ( r1_tarski(X0,X0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f92]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1597,plain,
% 2.99/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_21,plain,
% 2.99/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.99/0.98      | ~ m1_pre_topc(X2,X1)
% 2.99/0.98      | m1_pre_topc(X0,X2)
% 2.99/0.98      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 2.99/0.98      | ~ v2_pre_topc(X1)
% 2.99/0.98      | ~ l1_pre_topc(X1) ),
% 2.99/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1589,plain,
% 2.99/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 2.99/0.98      | m1_pre_topc(X2,X1) != iProver_top
% 2.99/0.98      | m1_pre_topc(X0,X2) = iProver_top
% 2.99/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
% 2.99/0.98      | v2_pre_topc(X1) != iProver_top
% 2.99/0.98      | l1_pre_topc(X1) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2992,plain,
% 2.99/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 2.99/0.98      | m1_pre_topc(X0,X0) = iProver_top
% 2.99/0.98      | v2_pre_topc(X1) != iProver_top
% 2.99/0.98      | l1_pre_topc(X1) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_1597,c_1589]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3816,plain,
% 2.99/0.98      ( m1_pre_topc(sK2,sK2) = iProver_top
% 2.99/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_1586,c_2992]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1867,plain,
% 2.99/0.98      ( ~ m1_pre_topc(X0,sK1)
% 2.99/0.98      | m1_pre_topc(sK2,X0)
% 2.99/0.98      | ~ m1_pre_topc(sK2,sK1)
% 2.99/0.98      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 2.99/0.98      | ~ v2_pre_topc(sK1)
% 2.99/0.98      | ~ l1_pre_topc(sK1) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_21]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2417,plain,
% 2.99/0.98      ( m1_pre_topc(sK2,sK2)
% 2.99/0.98      | ~ m1_pre_topc(sK2,sK1)
% 2.99/0.98      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2))
% 2.99/0.98      | ~ v2_pre_topc(sK1)
% 2.99/0.98      | ~ l1_pre_topc(sK1) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_1867]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2418,plain,
% 2.99/0.98      ( m1_pre_topc(sK2,sK2) = iProver_top
% 2.99/0.98      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.99/0.98      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 2.99/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_2417]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2601,plain,
% 2.99/0.98      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2602,plain,
% 2.99/0.98      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_2601]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3848,plain,
% 2.99/0.98      ( m1_pre_topc(sK2,sK2) = iProver_top ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_3816,c_39,c_40,c_42,c_2418,c_2602]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4890,plain,
% 2.99/0.98      ( m1_pre_topc(sK1,sK2) = iProver_top
% 2.99/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_3848,c_4881]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_7550,plain,
% 2.99/0.98      ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_7532,c_39,c_40,c_42,c_23,c_56,c_74,c_101,c_105,c_1835,
% 2.99/0.98                 c_1865,c_1877,c_2150,c_2639,c_4491,c_4495,c_4890]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_24,negated_conjecture,
% 2.99/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 2.99/0.98      inference(cnf_transformation,[],[f89]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1588,plain,
% 2.99/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_15,plain,
% 2.99/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.98      | ~ m1_pre_topc(X3,X1)
% 2.99/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.98      | ~ v2_pre_topc(X1)
% 2.99/0.98      | ~ v2_pre_topc(X2)
% 2.99/0.98      | v2_struct_0(X1)
% 2.99/0.98      | v2_struct_0(X2)
% 2.99/0.98      | ~ l1_pre_topc(X1)
% 2.99/0.98      | ~ l1_pre_topc(X2)
% 2.99/0.98      | ~ v1_funct_1(X0)
% 2.99/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.99/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_26,negated_conjecture,
% 2.99/0.98      ( v1_funct_1(sK3) ),
% 2.99/0.98      inference(cnf_transformation,[],[f87]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_563,plain,
% 2.99/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.98      | ~ m1_pre_topc(X3,X1)
% 2.99/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.98      | ~ v2_pre_topc(X1)
% 2.99/0.98      | ~ v2_pre_topc(X2)
% 2.99/0.98      | v2_struct_0(X1)
% 2.99/0.98      | v2_struct_0(X2)
% 2.99/0.98      | ~ l1_pre_topc(X1)
% 2.99/0.98      | ~ l1_pre_topc(X2)
% 2.99/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 2.99/0.98      | sK3 != X0 ),
% 2.99/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_564,plain,
% 2.99/0.98      ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
% 2.99/0.98      | ~ m1_pre_topc(X2,X0)
% 2.99/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.99/0.98      | ~ v2_pre_topc(X0)
% 2.99/0.98      | ~ v2_pre_topc(X1)
% 2.99/0.98      | v2_struct_0(X0)
% 2.99/0.98      | v2_struct_0(X1)
% 2.99/0.98      | ~ l1_pre_topc(X0)
% 2.99/0.98      | ~ l1_pre_topc(X1)
% 2.99/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2) ),
% 2.99/0.98      inference(unflattening,[status(thm)],[c_563]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1576,plain,
% 2.99/0.98      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2)
% 2.99/0.98      | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 2.99/0.98      | m1_pre_topc(X2,X0) != iProver_top
% 2.99/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.99/0.98      | v2_pre_topc(X1) != iProver_top
% 2.99/0.98      | v2_pre_topc(X0) != iProver_top
% 2.99/0.98      | v2_struct_0(X1) = iProver_top
% 2.99/0.98      | v2_struct_0(X0) = iProver_top
% 2.99/0.98      | l1_pre_topc(X1) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_564]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2347,plain,
% 2.99/0.98      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 2.99/0.98      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.99/0.98      | m1_pre_topc(X0,sK1) != iProver_top
% 2.99/0.98      | v2_pre_topc(sK0) != iProver_top
% 2.99/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.99/0.98      | v2_struct_0(sK0) = iProver_top
% 2.99/0.98      | v2_struct_0(sK1) = iProver_top
% 2.99/0.98      | l1_pre_topc(sK0) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_1588,c_1576]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_8,plain,
% 2.99/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.98      | ~ v1_funct_1(X0)
% 2.99/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.99/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_599,plain,
% 2.99/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 2.99/0.98      | sK3 != X0 ),
% 2.99/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_26]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_600,plain,
% 2.99/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.99/0.98      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 2.99/0.98      inference(unflattening,[status(thm)],[c_599]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1575,plain,
% 2.99/0.98      ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 2.99/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_600]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2140,plain,
% 2.99/0.98      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_1588,c_1575]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2348,plain,
% 2.99/0.98      ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
% 2.99/0.98      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.99/0.98      | m1_pre_topc(X0,sK1) != iProver_top
% 2.99/0.98      | v2_pre_topc(sK0) != iProver_top
% 2.99/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.99/0.98      | v2_struct_0(sK0) = iProver_top
% 2.99/0.98      | v2_struct_0(sK1) = iProver_top
% 2.99/0.98      | l1_pre_topc(sK0) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(demodulation,[status(thm)],[c_2347,c_2140]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_34,negated_conjecture,
% 2.99/0.98      ( ~ v2_struct_0(sK0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_35,plain,
% 2.99/0.98      ( v2_struct_0(sK0) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_33,negated_conjecture,
% 2.99/0.98      ( v2_pre_topc(sK0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_36,plain,
% 2.99/0.98      ( v2_pre_topc(sK0) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_32,negated_conjecture,
% 2.99/0.98      ( l1_pre_topc(sK0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_37,plain,
% 2.99/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_31,negated_conjecture,
% 2.99/0.98      ( ~ v2_struct_0(sK1) ),
% 2.99/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_38,plain,
% 2.99/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_25,negated_conjecture,
% 2.99/0.98      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 2.99/0.98      inference(cnf_transformation,[],[f88]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_44,plain,
% 2.99/0.98      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2388,plain,
% 2.99/0.98      ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
% 2.99/0.98      | m1_pre_topc(X0,sK1) != iProver_top ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_2348,c_35,c_36,c_37,c_38,c_39,c_40,c_44]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2396,plain,
% 2.99/0.98      ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_1586,c_2388]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_9,plain,
% 2.99/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_11,plain,
% 2.99/0.98      ( v2_struct_0(X0)
% 2.99/0.98      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.99/0.98      | ~ l1_struct_0(X0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_468,plain,
% 2.99/0.98      ( v2_struct_0(X0)
% 2.99/0.98      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.99/0.98      | ~ l1_pre_topc(X0) ),
% 2.99/0.98      inference(resolution,[status(thm)],[c_9,c_11]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_13,plain,
% 2.99/0.98      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 2.99/0.98      | ~ v1_funct_2(X4,X2,X3)
% 2.99/0.98      | ~ v1_funct_2(X4,X0,X1)
% 2.99/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.99/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.99/0.98      | v1_xboole_0(X1)
% 2.99/0.98      | v1_xboole_0(X3)
% 2.99/0.98      | ~ v1_funct_1(X4) ),
% 2.99/0.98      inference(cnf_transformation,[],[f94]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_22,negated_conjecture,
% 2.99/0.98      ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
% 2.99/0.98      inference(cnf_transformation,[],[f91]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_488,plain,
% 2.99/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.99/0.98      | ~ v1_funct_2(X0,X3,X4)
% 2.99/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.99/0.98      | v1_xboole_0(X4)
% 2.99/0.98      | v1_xboole_0(X2)
% 2.99/0.98      | ~ v1_funct_1(X0)
% 2.99/0.98      | k2_tmap_1(sK1,sK0,sK3,sK2) != X0
% 2.99/0.98      | u1_struct_0(sK2) != X1
% 2.99/0.98      | u1_struct_0(sK0) != X2
% 2.99/0.98      | u1_struct_0(sK0) != X4
% 2.99/0.98      | u1_struct_0(sK1) != X3
% 2.99/0.98      | sK3 != X0 ),
% 2.99/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_489,plain,
% 2.99/0.98      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.99/0.98      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.99/0.98      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.99/0.98      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.99/0.98      | v1_xboole_0(u1_struct_0(sK0))
% 2.99/0.98      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 2.99/0.98      | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 2.99/0.98      inference(unflattening,[status(thm)],[c_488]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_521,plain,
% 2.99/0.98      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.99/0.98      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.99/0.98      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.99/0.98      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.99/0.98      | v2_struct_0(X0)
% 2.99/0.98      | ~ l1_pre_topc(X0)
% 2.99/0.98      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 2.99/0.98      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 2.99/0.98      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 2.99/0.98      inference(resolution_lifted,[status(thm)],[c_468,c_489]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_611,plain,
% 2.99/0.98      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.99/0.98      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.99/0.98      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.99/0.98      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.99/0.98      | v2_struct_0(X0)
% 2.99/0.98      | ~ l1_pre_topc(X0)
% 2.99/0.98      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 2.99/0.98      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 2.99/0.98      inference(resolution_lifted,[status(thm)],[c_26,c_521]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_893,plain,
% 2.99/0.98      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.99/0.98      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.99/0.98      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.99/0.98      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.99/0.98      | sP0_iProver_split
% 2.99/0.98      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
% 2.99/0.98      inference(splitting,
% 2.99/0.98                [splitting(split),new_symbols(definition,[])],
% 2.99/0.98                [c_611]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1573,plain,
% 2.99/0.98      ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 2.99/0.98      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.99/0.98      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.99/0.98      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.99/0.98      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.99/0.98      | sP0_iProver_split = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_893]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2398,plain,
% 2.99/0.98      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 2.99/0.98      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.99/0.98      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.99/0.98      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.99/0.98      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.99/0.98      | sP0_iProver_split = iProver_top ),
% 2.99/0.98      inference(demodulation,[status(thm)],[c_2396,c_1573]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_892,plain,
% 2.99/0.98      ( v2_struct_0(X0)
% 2.99/0.98      | ~ l1_pre_topc(X0)
% 2.99/0.98      | u1_struct_0(X0) != u1_struct_0(sK0)
% 2.99/0.98      | ~ sP0_iProver_split ),
% 2.99/0.98      inference(splitting,
% 2.99/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.99/0.98                [c_611]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1574,plain,
% 2.99/0.98      ( u1_struct_0(X0) != u1_struct_0(sK0)
% 2.99/0.98      | v2_struct_0(X0) = iProver_top
% 2.99/0.98      | l1_pre_topc(X0) != iProver_top
% 2.99/0.98      | sP0_iProver_split != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_892]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2242,plain,
% 2.99/0.98      ( v2_struct_0(sK0) = iProver_top
% 2.99/0.98      | l1_pre_topc(sK0) != iProver_top
% 2.99/0.98      | sP0_iProver_split != iProver_top ),
% 2.99/0.98      inference(equality_resolution,[status(thm)],[c_1574]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2431,plain,
% 2.99/0.98      ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.99/0.98      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.99/0.98      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.99/0.98      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.99/0.98      | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_2398,c_35,c_37,c_2242]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2432,plain,
% 2.99/0.98      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 2.99/0.98      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.99/0.98      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.99/0.98      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.99/0.98      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.99/0.98      inference(renaming,[status(thm)],[c_2431]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_7557,plain,
% 2.99/0.98      ( k7_relat_1(sK3,u1_struct_0(sK1)) != sK3
% 2.99/0.98      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.99/0.98      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.99/0.98      inference(demodulation,[status(thm)],[c_7550,c_2432]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_7,plain,
% 2.99/0.98      ( v4_relat_1(X0,X1)
% 2.99/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.99/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_5,plain,
% 2.99/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.99/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_448,plain,
% 2.99/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.98      | ~ v1_relat_1(X0)
% 2.99/0.98      | k7_relat_1(X0,X1) = X0 ),
% 2.99/0.98      inference(resolution,[status(thm)],[c_7,c_5]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_6,plain,
% 2.99/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.98      | v1_relat_1(X0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_452,plain,
% 2.99/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.98      | k7_relat_1(X0,X1) = X0 ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_448,c_7,c_6,c_5]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1577,plain,
% 2.99/0.98      ( k7_relat_1(X0,X1) = X0
% 2.99/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2443,plain,
% 2.99/0.98      ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_1588,c_1577]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_7568,plain,
% 2.99/0.98      ( sK3 != sK3
% 2.99/0.98      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.99/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.99/0.98      inference(light_normalisation,[status(thm)],[c_7557,c_2443]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_7569,plain,
% 2.99/0.98      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.99/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.99/0.98      inference(equality_resolution_simp,[status(thm)],[c_7568]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_45,plain,
% 2.99/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(contradiction,plain,
% 2.99/0.98      ( $false ),
% 2.99/0.98      inference(minisat,[status(thm)],[c_7569,c_45,c_44]) ).
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.99/0.98  
% 2.99/0.98  ------                               Statistics
% 2.99/0.98  
% 2.99/0.98  ------ General
% 2.99/0.98  
% 2.99/0.98  abstr_ref_over_cycles:                  0
% 2.99/0.98  abstr_ref_under_cycles:                 0
% 2.99/0.98  gc_basic_clause_elim:                   0
% 2.99/0.98  forced_gc_time:                         0
% 2.99/0.98  parsing_time:                           0.01
% 2.99/0.98  unif_index_cands_time:                  0.
% 2.99/0.98  unif_index_add_time:                    0.
% 2.99/0.98  orderings_time:                         0.
% 2.99/0.98  out_proof_time:                         0.012
% 2.99/0.98  total_time:                             0.23
% 2.99/0.98  num_of_symbols:                         57
% 2.99/0.98  num_of_terms:                           4056
% 2.99/0.98  
% 2.99/0.98  ------ Preprocessing
% 2.99/0.98  
% 2.99/0.98  num_of_splits:                          1
% 2.99/0.98  num_of_split_atoms:                     1
% 2.99/0.98  num_of_reused_defs:                     0
% 2.99/0.98  num_eq_ax_congr_red:                    9
% 2.99/0.98  num_of_sem_filtered_clauses:            1
% 2.99/0.98  num_of_subtypes:                        0
% 2.99/0.98  monotx_restored_types:                  0
% 2.99/0.98  sat_num_of_epr_types:                   0
% 2.99/0.98  sat_num_of_non_cyclic_types:            0
% 2.99/0.98  sat_guarded_non_collapsed_types:        0
% 2.99/0.98  num_pure_diseq_elim:                    0
% 2.99/0.98  simp_replaced_by:                       0
% 2.99/0.98  res_preprocessed:                       148
% 2.99/0.98  prep_upred:                             0
% 2.99/0.98  prep_unflattend:                        13
% 2.99/0.98  smt_new_axioms:                         0
% 2.99/0.98  pred_elim_cands:                        7
% 2.99/0.98  pred_elim:                              6
% 2.99/0.98  pred_elim_cl:                           7
% 2.99/0.98  pred_elim_cycles:                       8
% 2.99/0.98  merged_defs:                            8
% 2.99/0.98  merged_defs_ncl:                        0
% 2.99/0.98  bin_hyper_res:                          8
% 2.99/0.98  prep_cycles:                            4
% 2.99/0.98  pred_elim_time:                         0.007
% 2.99/0.98  splitting_time:                         0.
% 2.99/0.98  sem_filter_time:                        0.
% 2.99/0.98  monotx_time:                            0.001
% 2.99/0.98  subtype_inf_time:                       0.
% 2.99/0.98  
% 2.99/0.98  ------ Problem properties
% 2.99/0.98  
% 2.99/0.98  clauses:                                27
% 2.99/0.98  conjectures:                            11
% 2.99/0.98  epr:                                    11
% 2.99/0.98  horn:                                   26
% 2.99/0.98  ground:                                 12
% 2.99/0.98  unary:                                  12
% 2.99/0.98  binary:                                 4
% 2.99/0.98  lits:                                   73
% 2.99/0.98  lits_eq:                                7
% 2.99/0.98  fd_pure:                                0
% 2.99/0.98  fd_pseudo:                              0
% 2.99/0.98  fd_cond:                                0
% 2.99/0.98  fd_pseudo_cond:                         1
% 2.99/0.98  ac_symbols:                             0
% 2.99/0.98  
% 2.99/0.98  ------ Propositional Solver
% 2.99/0.98  
% 2.99/0.98  prop_solver_calls:                      29
% 2.99/0.98  prop_fast_solver_calls:                 1315
% 2.99/0.98  smt_solver_calls:                       0
% 2.99/0.98  smt_fast_solver_calls:                  0
% 2.99/0.98  prop_num_of_clauses:                    2206
% 2.99/0.98  prop_preprocess_simplified:             6380
% 2.99/0.98  prop_fo_subsumed:                       83
% 2.99/0.98  prop_solver_time:                       0.
% 2.99/0.98  smt_solver_time:                        0.
% 2.99/0.98  smt_fast_solver_time:                   0.
% 2.99/0.98  prop_fast_solver_time:                  0.
% 2.99/0.98  prop_unsat_core_time:                   0.
% 2.99/0.98  
% 2.99/0.98  ------ QBF
% 2.99/0.98  
% 2.99/0.98  qbf_q_res:                              0
% 2.99/0.98  qbf_num_tautologies:                    0
% 2.99/0.98  qbf_prep_cycles:                        0
% 2.99/0.98  
% 2.99/0.98  ------ BMC1
% 2.99/0.98  
% 2.99/0.98  bmc1_current_bound:                     -1
% 2.99/0.98  bmc1_last_solved_bound:                 -1
% 2.99/0.98  bmc1_unsat_core_size:                   -1
% 2.99/0.98  bmc1_unsat_core_parents_size:           -1
% 2.99/0.98  bmc1_merge_next_fun:                    0
% 2.99/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.99/0.98  
% 2.99/0.98  ------ Instantiation
% 2.99/0.98  
% 2.99/0.98  inst_num_of_clauses:                    636
% 2.99/0.98  inst_num_in_passive:                    103
% 2.99/0.98  inst_num_in_active:                     459
% 2.99/0.98  inst_num_in_unprocessed:                74
% 2.99/0.98  inst_num_of_loops:                      490
% 2.99/0.98  inst_num_of_learning_restarts:          0
% 2.99/0.98  inst_num_moves_active_passive:          27
% 2.99/0.98  inst_lit_activity:                      0
% 2.99/0.98  inst_lit_activity_moves:                0
% 2.99/0.98  inst_num_tautologies:                   0
% 2.99/0.98  inst_num_prop_implied:                  0
% 2.99/0.98  inst_num_existing_simplified:           0
% 2.99/0.98  inst_num_eq_res_simplified:             0
% 2.99/0.98  inst_num_child_elim:                    0
% 2.99/0.98  inst_num_of_dismatching_blockings:      303
% 2.99/0.98  inst_num_of_non_proper_insts:           1082
% 2.99/0.98  inst_num_of_duplicates:                 0
% 2.99/0.98  inst_inst_num_from_inst_to_res:         0
% 2.99/0.98  inst_dismatching_checking_time:         0.
% 2.99/0.98  
% 2.99/0.98  ------ Resolution
% 2.99/0.98  
% 2.99/0.98  res_num_of_clauses:                     0
% 2.99/0.98  res_num_in_passive:                     0
% 2.99/0.98  res_num_in_active:                      0
% 2.99/0.98  res_num_of_loops:                       152
% 2.99/0.98  res_forward_subset_subsumed:            103
% 2.99/0.98  res_backward_subset_subsumed:           4
% 2.99/0.98  res_forward_subsumed:                   0
% 2.99/0.98  res_backward_subsumed:                  0
% 2.99/0.98  res_forward_subsumption_resolution:     0
% 2.99/0.98  res_backward_subsumption_resolution:    0
% 2.99/0.98  res_clause_to_clause_subsumption:       698
% 2.99/0.98  res_orphan_elimination:                 0
% 2.99/0.98  res_tautology_del:                      85
% 2.99/0.98  res_num_eq_res_simplified:              0
% 2.99/0.98  res_num_sel_changes:                    0
% 2.99/0.98  res_moves_from_active_to_pass:          0
% 2.99/0.98  
% 2.99/0.98  ------ Superposition
% 2.99/0.98  
% 2.99/0.98  sup_time_total:                         0.
% 2.99/0.98  sup_time_generating:                    0.
% 2.99/0.98  sup_time_sim_full:                      0.
% 2.99/0.98  sup_time_sim_immed:                     0.
% 2.99/0.98  
% 2.99/0.98  sup_num_of_clauses:                     141
% 2.99/0.98  sup_num_in_active:                      73
% 2.99/0.98  sup_num_in_passive:                     68
% 2.99/0.98  sup_num_of_loops:                       97
% 2.99/0.98  sup_fw_superposition:                   125
% 2.99/0.98  sup_bw_superposition:                   107
% 2.99/0.98  sup_immediate_simplified:               75
% 2.99/0.98  sup_given_eliminated:                   0
% 2.99/0.98  comparisons_done:                       0
% 2.99/0.98  comparisons_avoided:                    0
% 2.99/0.98  
% 2.99/0.98  ------ Simplifications
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  sim_fw_subset_subsumed:                 26
% 2.99/0.98  sim_bw_subset_subsumed:                 16
% 2.99/0.98  sim_fw_subsumed:                        23
% 2.99/0.98  sim_bw_subsumed:                        2
% 2.99/0.98  sim_fw_subsumption_res:                 2
% 2.99/0.98  sim_bw_subsumption_res:                 0
% 2.99/0.98  sim_tautology_del:                      16
% 2.99/0.98  sim_eq_tautology_del:                   14
% 2.99/0.98  sim_eq_res_simp:                        1
% 2.99/0.98  sim_fw_demodulated:                     4
% 2.99/0.98  sim_bw_demodulated:                     24
% 2.99/0.98  sim_light_normalised:                   30
% 2.99/0.98  sim_joinable_taut:                      0
% 2.99/0.98  sim_joinable_simp:                      0
% 2.99/0.98  sim_ac_normalised:                      0
% 2.99/0.98  sim_smt_subsumption:                    0
% 2.99/0.98  
%------------------------------------------------------------------------------
