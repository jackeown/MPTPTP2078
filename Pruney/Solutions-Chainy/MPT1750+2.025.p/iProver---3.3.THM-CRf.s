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
% DateTime   : Thu Dec  3 12:22:27 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 490 expanded)
%              Number of clauses        :   89 ( 139 expanded)
%              Number of leaves         :   20 ( 153 expanded)
%              Depth                    :   20
%              Number of atoms          :  678 (4240 expanded)
%              Number of equality atoms :  208 ( 588 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
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
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f47,f46,f45,f44])).

fof(f76,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f68,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f84,plain,(
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
    inference(equality_resolution,[],[f65])).

fof(f81,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1480,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1484,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1487,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3014,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1484,c_1487])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1490,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3595,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3014,c_1490])).

cnf(c_3800,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3014,c_3595])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_68,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4287,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3800,c_68,c_3014,c_3595])).

cnf(c_4288,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4287])).

cnf(c_4297,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_pre_topc(sK1,sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_4288])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_38,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_19,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_45,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_47,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_60,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_62,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_1486,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2457,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_1486])).

cnf(c_21,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_12,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1485,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3024,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_1485])).

cnf(c_3041,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3024])).

cnf(c_4573,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4297,c_38,c_47,c_62,c_2457,c_3041])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1482,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_530,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_531,plain,
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
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_1470,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2)
    | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_2074,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1482,c_1470])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_567,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_1469,plain,
    ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_1903,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1482,c_1469])).

cnf(c_2075,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2074,c_1903])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_33,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_34,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_35,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_36,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_37,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_42,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2161,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2075,c_33,c_34,c_35,c_36,c_37,c_38,c_42])).

cnf(c_2169,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_1480,c_2161])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_435,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_9,c_11])).

cnf(c_15,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_20,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_455,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_456,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_488,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_435,c_456])).

cnf(c_578,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_24,c_488])).

cnf(c_842,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | sP0_iProver_split
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_578])).

cnf(c_1467,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_842])).

cnf(c_2171,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2169,c_1467])).

cnf(c_841,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_578])).

cnf(c_1468,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK0)
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_841])).

cnf(c_1986,plain,
    ( v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1468])).

cnf(c_2243,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2171,c_33,c_35,c_1986])).

cnf(c_2244,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2243])).

cnf(c_4576,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4573,c_2244])).

cnf(c_7,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_7,c_5])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_7,c_6,c_5])).

cnf(c_1471,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_2255,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
    inference(superposition,[status(thm)],[c_1482,c_1471])).

cnf(c_4587,plain,
    ( sK3 != sK3
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4576,c_2255])).

cnf(c_4588,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4587])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4588,c_43,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:50:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.86/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/0.96  
% 2.86/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.86/0.96  
% 2.86/0.96  ------  iProver source info
% 2.86/0.96  
% 2.86/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.86/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.86/0.96  git: non_committed_changes: false
% 2.86/0.96  git: last_make_outside_of_git: false
% 2.86/0.96  
% 2.86/0.96  ------ 
% 2.86/0.96  
% 2.86/0.96  ------ Input Options
% 2.86/0.96  
% 2.86/0.96  --out_options                           all
% 2.86/0.96  --tptp_safe_out                         true
% 2.86/0.96  --problem_path                          ""
% 2.86/0.96  --include_path                          ""
% 2.86/0.96  --clausifier                            res/vclausify_rel
% 2.86/0.96  --clausifier_options                    --mode clausify
% 2.86/0.96  --stdin                                 false
% 2.86/0.96  --stats_out                             all
% 2.86/0.96  
% 2.86/0.96  ------ General Options
% 2.86/0.96  
% 2.86/0.96  --fof                                   false
% 2.86/0.96  --time_out_real                         305.
% 2.86/0.96  --time_out_virtual                      -1.
% 2.86/0.96  --symbol_type_check                     false
% 2.86/0.96  --clausify_out                          false
% 2.86/0.96  --sig_cnt_out                           false
% 2.86/0.96  --trig_cnt_out                          false
% 2.86/0.96  --trig_cnt_out_tolerance                1.
% 2.86/0.96  --trig_cnt_out_sk_spl                   false
% 2.86/0.96  --abstr_cl_out                          false
% 2.86/0.96  
% 2.86/0.96  ------ Global Options
% 2.86/0.96  
% 2.86/0.96  --schedule                              default
% 2.86/0.96  --add_important_lit                     false
% 2.86/0.96  --prop_solver_per_cl                    1000
% 2.86/0.96  --min_unsat_core                        false
% 2.86/0.96  --soft_assumptions                      false
% 2.86/0.96  --soft_lemma_size                       3
% 2.86/0.96  --prop_impl_unit_size                   0
% 2.86/0.96  --prop_impl_unit                        []
% 2.86/0.96  --share_sel_clauses                     true
% 2.86/0.96  --reset_solvers                         false
% 2.86/0.96  --bc_imp_inh                            [conj_cone]
% 2.86/0.96  --conj_cone_tolerance                   3.
% 2.86/0.96  --extra_neg_conj                        none
% 2.86/0.96  --large_theory_mode                     true
% 2.86/0.96  --prolific_symb_bound                   200
% 2.86/0.96  --lt_threshold                          2000
% 2.86/0.96  --clause_weak_htbl                      true
% 2.86/0.96  --gc_record_bc_elim                     false
% 2.86/0.96  
% 2.86/0.96  ------ Preprocessing Options
% 2.86/0.96  
% 2.86/0.96  --preprocessing_flag                    true
% 2.86/0.96  --time_out_prep_mult                    0.1
% 2.86/0.96  --splitting_mode                        input
% 2.86/0.96  --splitting_grd                         true
% 2.86/0.96  --splitting_cvd                         false
% 2.86/0.96  --splitting_cvd_svl                     false
% 2.86/0.96  --splitting_nvd                         32
% 2.86/0.96  --sub_typing                            true
% 2.86/0.96  --prep_gs_sim                           true
% 2.86/0.96  --prep_unflatten                        true
% 2.86/0.96  --prep_res_sim                          true
% 2.86/0.96  --prep_upred                            true
% 2.86/0.96  --prep_sem_filter                       exhaustive
% 2.86/0.96  --prep_sem_filter_out                   false
% 2.86/0.96  --pred_elim                             true
% 2.86/0.96  --res_sim_input                         true
% 2.86/0.96  --eq_ax_congr_red                       true
% 2.86/0.96  --pure_diseq_elim                       true
% 2.86/0.96  --brand_transform                       false
% 2.86/0.96  --non_eq_to_eq                          false
% 2.86/0.96  --prep_def_merge                        true
% 2.86/0.96  --prep_def_merge_prop_impl              false
% 2.86/0.96  --prep_def_merge_mbd                    true
% 2.86/0.96  --prep_def_merge_tr_red                 false
% 2.86/0.96  --prep_def_merge_tr_cl                  false
% 2.86/0.96  --smt_preprocessing                     true
% 2.86/0.96  --smt_ac_axioms                         fast
% 2.86/0.96  --preprocessed_out                      false
% 2.86/0.96  --preprocessed_stats                    false
% 2.86/0.96  
% 2.86/0.96  ------ Abstraction refinement Options
% 2.86/0.96  
% 2.86/0.96  --abstr_ref                             []
% 2.86/0.96  --abstr_ref_prep                        false
% 2.86/0.96  --abstr_ref_until_sat                   false
% 2.86/0.96  --abstr_ref_sig_restrict                funpre
% 2.86/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.86/0.96  --abstr_ref_under                       []
% 2.86/0.96  
% 2.86/0.96  ------ SAT Options
% 2.86/0.96  
% 2.86/0.96  --sat_mode                              false
% 2.86/0.96  --sat_fm_restart_options                ""
% 2.86/0.96  --sat_gr_def                            false
% 2.86/0.96  --sat_epr_types                         true
% 2.86/0.96  --sat_non_cyclic_types                  false
% 2.86/0.96  --sat_finite_models                     false
% 2.86/0.96  --sat_fm_lemmas                         false
% 2.86/0.96  --sat_fm_prep                           false
% 2.86/0.96  --sat_fm_uc_incr                        true
% 2.86/0.96  --sat_out_model                         small
% 2.86/0.96  --sat_out_clauses                       false
% 2.86/0.96  
% 2.86/0.96  ------ QBF Options
% 2.86/0.96  
% 2.86/0.96  --qbf_mode                              false
% 2.86/0.96  --qbf_elim_univ                         false
% 2.86/0.96  --qbf_dom_inst                          none
% 2.86/0.96  --qbf_dom_pre_inst                      false
% 2.86/0.96  --qbf_sk_in                             false
% 2.86/0.96  --qbf_pred_elim                         true
% 2.86/0.96  --qbf_split                             512
% 2.86/0.96  
% 2.86/0.96  ------ BMC1 Options
% 2.86/0.96  
% 2.86/0.96  --bmc1_incremental                      false
% 2.86/0.96  --bmc1_axioms                           reachable_all
% 2.86/0.96  --bmc1_min_bound                        0
% 2.86/0.96  --bmc1_max_bound                        -1
% 2.86/0.96  --bmc1_max_bound_default                -1
% 2.86/0.96  --bmc1_symbol_reachability              true
% 2.86/0.96  --bmc1_property_lemmas                  false
% 2.86/0.96  --bmc1_k_induction                      false
% 2.86/0.96  --bmc1_non_equiv_states                 false
% 2.86/0.96  --bmc1_deadlock                         false
% 2.86/0.96  --bmc1_ucm                              false
% 2.86/0.96  --bmc1_add_unsat_core                   none
% 2.86/0.96  --bmc1_unsat_core_children              false
% 2.86/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.86/0.96  --bmc1_out_stat                         full
% 2.86/0.96  --bmc1_ground_init                      false
% 2.86/0.96  --bmc1_pre_inst_next_state              false
% 2.86/0.96  --bmc1_pre_inst_state                   false
% 2.86/0.96  --bmc1_pre_inst_reach_state             false
% 2.86/0.96  --bmc1_out_unsat_core                   false
% 2.86/0.96  --bmc1_aig_witness_out                  false
% 2.86/0.96  --bmc1_verbose                          false
% 2.86/0.96  --bmc1_dump_clauses_tptp                false
% 2.86/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.86/0.96  --bmc1_dump_file                        -
% 2.86/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.86/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.86/0.96  --bmc1_ucm_extend_mode                  1
% 2.86/0.96  --bmc1_ucm_init_mode                    2
% 2.86/0.96  --bmc1_ucm_cone_mode                    none
% 2.86/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.86/0.96  --bmc1_ucm_relax_model                  4
% 2.86/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.86/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.86/0.96  --bmc1_ucm_layered_model                none
% 2.86/0.96  --bmc1_ucm_max_lemma_size               10
% 2.86/0.96  
% 2.86/0.96  ------ AIG Options
% 2.86/0.96  
% 2.86/0.96  --aig_mode                              false
% 2.86/0.96  
% 2.86/0.96  ------ Instantiation Options
% 2.86/0.96  
% 2.86/0.96  --instantiation_flag                    true
% 2.86/0.96  --inst_sos_flag                         false
% 2.86/0.96  --inst_sos_phase                        true
% 2.86/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.86/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.86/0.96  --inst_lit_sel_side                     num_symb
% 2.86/0.96  --inst_solver_per_active                1400
% 2.86/0.96  --inst_solver_calls_frac                1.
% 2.86/0.96  --inst_passive_queue_type               priority_queues
% 2.86/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.86/0.96  --inst_passive_queues_freq              [25;2]
% 2.86/0.96  --inst_dismatching                      true
% 2.86/0.96  --inst_eager_unprocessed_to_passive     true
% 2.86/0.96  --inst_prop_sim_given                   true
% 2.86/0.96  --inst_prop_sim_new                     false
% 2.86/0.96  --inst_subs_new                         false
% 2.86/0.96  --inst_eq_res_simp                      false
% 2.86/0.96  --inst_subs_given                       false
% 2.86/0.96  --inst_orphan_elimination               true
% 2.86/0.96  --inst_learning_loop_flag               true
% 2.86/0.96  --inst_learning_start                   3000
% 2.86/0.96  --inst_learning_factor                  2
% 2.86/0.96  --inst_start_prop_sim_after_learn       3
% 2.86/0.96  --inst_sel_renew                        solver
% 2.86/0.96  --inst_lit_activity_flag                true
% 2.86/0.96  --inst_restr_to_given                   false
% 2.86/0.96  --inst_activity_threshold               500
% 2.86/0.96  --inst_out_proof                        true
% 2.86/0.96  
% 2.86/0.96  ------ Resolution Options
% 2.86/0.96  
% 2.86/0.96  --resolution_flag                       true
% 2.86/0.96  --res_lit_sel                           adaptive
% 2.86/0.96  --res_lit_sel_side                      none
% 2.86/0.96  --res_ordering                          kbo
% 2.86/0.96  --res_to_prop_solver                    active
% 2.86/0.96  --res_prop_simpl_new                    false
% 2.86/0.96  --res_prop_simpl_given                  true
% 2.86/0.96  --res_passive_queue_type                priority_queues
% 2.86/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.86/0.96  --res_passive_queues_freq               [15;5]
% 2.86/0.96  --res_forward_subs                      full
% 2.86/0.96  --res_backward_subs                     full
% 2.86/0.96  --res_forward_subs_resolution           true
% 2.86/0.96  --res_backward_subs_resolution          true
% 2.86/0.96  --res_orphan_elimination                true
% 2.86/0.96  --res_time_limit                        2.
% 2.86/0.96  --res_out_proof                         true
% 2.86/0.96  
% 2.86/0.96  ------ Superposition Options
% 2.86/0.96  
% 2.86/0.96  --superposition_flag                    true
% 2.86/0.96  --sup_passive_queue_type                priority_queues
% 2.86/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.86/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.86/0.96  --demod_completeness_check              fast
% 2.86/0.96  --demod_use_ground                      true
% 2.86/0.96  --sup_to_prop_solver                    passive
% 2.86/0.96  --sup_prop_simpl_new                    true
% 2.86/0.96  --sup_prop_simpl_given                  true
% 2.86/0.96  --sup_fun_splitting                     false
% 2.86/0.96  --sup_smt_interval                      50000
% 2.86/0.96  
% 2.86/0.96  ------ Superposition Simplification Setup
% 2.86/0.96  
% 2.86/0.96  --sup_indices_passive                   []
% 2.86/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.86/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.96  --sup_full_bw                           [BwDemod]
% 2.86/0.96  --sup_immed_triv                        [TrivRules]
% 2.86/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.86/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.96  --sup_immed_bw_main                     []
% 2.86/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.86/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/0.96  
% 2.86/0.96  ------ Combination Options
% 2.86/0.96  
% 2.86/0.96  --comb_res_mult                         3
% 2.86/0.96  --comb_sup_mult                         2
% 2.86/0.96  --comb_inst_mult                        10
% 2.86/0.96  
% 2.86/0.96  ------ Debug Options
% 2.86/0.96  
% 2.86/0.96  --dbg_backtrace                         false
% 2.86/0.96  --dbg_dump_prop_clauses                 false
% 2.86/0.96  --dbg_dump_prop_clauses_file            -
% 2.86/0.96  --dbg_out_stat                          false
% 2.86/0.96  ------ Parsing...
% 2.86/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.86/0.96  
% 2.86/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.86/0.96  
% 2.86/0.96  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.86/0.96  
% 2.86/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.86/0.96  ------ Proving...
% 2.86/0.96  ------ Problem Properties 
% 2.86/0.96  
% 2.86/0.96  
% 2.86/0.96  clauses                                 25
% 2.86/0.96  conjectures                             11
% 2.86/0.96  EPR                                     12
% 2.86/0.96  Horn                                    24
% 2.86/0.96  unary                                   12
% 2.86/0.96  binary                                  5
% 2.86/0.96  lits                                    57
% 2.86/0.96  lits eq                                 7
% 2.86/0.96  fd_pure                                 0
% 2.86/0.96  fd_pseudo                               0
% 2.86/0.96  fd_cond                                 0
% 2.86/0.96  fd_pseudo_cond                          1
% 2.86/0.96  AC symbols                              0
% 2.86/0.96  
% 2.86/0.96  ------ Schedule dynamic 5 is on 
% 2.86/0.96  
% 2.86/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.86/0.96  
% 2.86/0.96  
% 2.86/0.96  ------ 
% 2.86/0.96  Current options:
% 2.86/0.96  ------ 
% 2.86/0.96  
% 2.86/0.96  ------ Input Options
% 2.86/0.96  
% 2.86/0.96  --out_options                           all
% 2.86/0.96  --tptp_safe_out                         true
% 2.86/0.96  --problem_path                          ""
% 2.86/0.96  --include_path                          ""
% 2.86/0.96  --clausifier                            res/vclausify_rel
% 2.86/0.96  --clausifier_options                    --mode clausify
% 2.86/0.96  --stdin                                 false
% 2.86/0.96  --stats_out                             all
% 2.86/0.96  
% 2.86/0.96  ------ General Options
% 2.86/0.96  
% 2.86/0.96  --fof                                   false
% 2.86/0.96  --time_out_real                         305.
% 2.86/0.96  --time_out_virtual                      -1.
% 2.86/0.96  --symbol_type_check                     false
% 2.86/0.96  --clausify_out                          false
% 2.86/0.96  --sig_cnt_out                           false
% 2.86/0.96  --trig_cnt_out                          false
% 2.86/0.96  --trig_cnt_out_tolerance                1.
% 2.86/0.96  --trig_cnt_out_sk_spl                   false
% 2.86/0.96  --abstr_cl_out                          false
% 2.86/0.96  
% 2.86/0.96  ------ Global Options
% 2.86/0.96  
% 2.86/0.96  --schedule                              default
% 2.86/0.96  --add_important_lit                     false
% 2.86/0.96  --prop_solver_per_cl                    1000
% 2.86/0.96  --min_unsat_core                        false
% 2.86/0.96  --soft_assumptions                      false
% 2.86/0.96  --soft_lemma_size                       3
% 2.86/0.96  --prop_impl_unit_size                   0
% 2.86/0.96  --prop_impl_unit                        []
% 2.86/0.96  --share_sel_clauses                     true
% 2.86/0.96  --reset_solvers                         false
% 2.86/0.96  --bc_imp_inh                            [conj_cone]
% 2.86/0.96  --conj_cone_tolerance                   3.
% 2.86/0.96  --extra_neg_conj                        none
% 2.86/0.96  --large_theory_mode                     true
% 2.86/0.96  --prolific_symb_bound                   200
% 2.86/0.96  --lt_threshold                          2000
% 2.86/0.96  --clause_weak_htbl                      true
% 2.86/0.96  --gc_record_bc_elim                     false
% 2.86/0.96  
% 2.86/0.96  ------ Preprocessing Options
% 2.86/0.96  
% 2.86/0.96  --preprocessing_flag                    true
% 2.86/0.96  --time_out_prep_mult                    0.1
% 2.86/0.96  --splitting_mode                        input
% 2.86/0.96  --splitting_grd                         true
% 2.86/0.96  --splitting_cvd                         false
% 2.86/0.96  --splitting_cvd_svl                     false
% 2.86/0.96  --splitting_nvd                         32
% 2.86/0.96  --sub_typing                            true
% 2.86/0.96  --prep_gs_sim                           true
% 2.86/0.96  --prep_unflatten                        true
% 2.86/0.96  --prep_res_sim                          true
% 2.86/0.96  --prep_upred                            true
% 2.86/0.96  --prep_sem_filter                       exhaustive
% 2.86/0.96  --prep_sem_filter_out                   false
% 2.86/0.96  --pred_elim                             true
% 2.86/0.96  --res_sim_input                         true
% 2.86/0.96  --eq_ax_congr_red                       true
% 2.86/0.96  --pure_diseq_elim                       true
% 2.86/0.96  --brand_transform                       false
% 2.86/0.96  --non_eq_to_eq                          false
% 2.86/0.96  --prep_def_merge                        true
% 2.86/0.96  --prep_def_merge_prop_impl              false
% 2.86/0.96  --prep_def_merge_mbd                    true
% 2.86/0.96  --prep_def_merge_tr_red                 false
% 2.86/0.96  --prep_def_merge_tr_cl                  false
% 2.86/0.96  --smt_preprocessing                     true
% 2.86/0.96  --smt_ac_axioms                         fast
% 2.86/0.96  --preprocessed_out                      false
% 2.86/0.96  --preprocessed_stats                    false
% 2.86/0.96  
% 2.86/0.96  ------ Abstraction refinement Options
% 2.86/0.96  
% 2.86/0.96  --abstr_ref                             []
% 2.86/0.96  --abstr_ref_prep                        false
% 2.86/0.96  --abstr_ref_until_sat                   false
% 2.86/0.96  --abstr_ref_sig_restrict                funpre
% 2.86/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.86/0.96  --abstr_ref_under                       []
% 2.86/0.96  
% 2.86/0.96  ------ SAT Options
% 2.86/0.96  
% 2.86/0.96  --sat_mode                              false
% 2.86/0.96  --sat_fm_restart_options                ""
% 2.86/0.96  --sat_gr_def                            false
% 2.86/0.96  --sat_epr_types                         true
% 2.86/0.96  --sat_non_cyclic_types                  false
% 2.86/0.96  --sat_finite_models                     false
% 2.86/0.96  --sat_fm_lemmas                         false
% 2.86/0.96  --sat_fm_prep                           false
% 2.86/0.96  --sat_fm_uc_incr                        true
% 2.86/0.96  --sat_out_model                         small
% 2.86/0.96  --sat_out_clauses                       false
% 2.86/0.96  
% 2.86/0.96  ------ QBF Options
% 2.86/0.96  
% 2.86/0.96  --qbf_mode                              false
% 2.86/0.96  --qbf_elim_univ                         false
% 2.86/0.96  --qbf_dom_inst                          none
% 2.86/0.96  --qbf_dom_pre_inst                      false
% 2.86/0.96  --qbf_sk_in                             false
% 2.86/0.96  --qbf_pred_elim                         true
% 2.86/0.96  --qbf_split                             512
% 2.86/0.96  
% 2.86/0.96  ------ BMC1 Options
% 2.86/0.96  
% 2.86/0.96  --bmc1_incremental                      false
% 2.86/0.96  --bmc1_axioms                           reachable_all
% 2.86/0.96  --bmc1_min_bound                        0
% 2.86/0.96  --bmc1_max_bound                        -1
% 2.86/0.96  --bmc1_max_bound_default                -1
% 2.86/0.96  --bmc1_symbol_reachability              true
% 2.86/0.96  --bmc1_property_lemmas                  false
% 2.86/0.96  --bmc1_k_induction                      false
% 2.86/0.96  --bmc1_non_equiv_states                 false
% 2.86/0.96  --bmc1_deadlock                         false
% 2.86/0.96  --bmc1_ucm                              false
% 2.86/0.96  --bmc1_add_unsat_core                   none
% 2.86/0.96  --bmc1_unsat_core_children              false
% 2.86/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.86/0.96  --bmc1_out_stat                         full
% 2.86/0.96  --bmc1_ground_init                      false
% 2.86/0.96  --bmc1_pre_inst_next_state              false
% 2.86/0.96  --bmc1_pre_inst_state                   false
% 2.86/0.96  --bmc1_pre_inst_reach_state             false
% 2.86/0.96  --bmc1_out_unsat_core                   false
% 2.86/0.96  --bmc1_aig_witness_out                  false
% 2.86/0.96  --bmc1_verbose                          false
% 2.86/0.96  --bmc1_dump_clauses_tptp                false
% 2.86/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.86/0.96  --bmc1_dump_file                        -
% 2.86/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.86/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.86/0.96  --bmc1_ucm_extend_mode                  1
% 2.86/0.96  --bmc1_ucm_init_mode                    2
% 2.86/0.96  --bmc1_ucm_cone_mode                    none
% 2.86/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.86/0.96  --bmc1_ucm_relax_model                  4
% 2.86/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.86/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.86/0.96  --bmc1_ucm_layered_model                none
% 2.86/0.96  --bmc1_ucm_max_lemma_size               10
% 2.86/0.96  
% 2.86/0.96  ------ AIG Options
% 2.86/0.96  
% 2.86/0.96  --aig_mode                              false
% 2.86/0.96  
% 2.86/0.96  ------ Instantiation Options
% 2.86/0.96  
% 2.86/0.96  --instantiation_flag                    true
% 2.86/0.96  --inst_sos_flag                         false
% 2.86/0.96  --inst_sos_phase                        true
% 2.86/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.86/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.86/0.96  --inst_lit_sel_side                     none
% 2.86/0.96  --inst_solver_per_active                1400
% 2.86/0.96  --inst_solver_calls_frac                1.
% 2.86/0.96  --inst_passive_queue_type               priority_queues
% 2.86/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.86/0.96  --inst_passive_queues_freq              [25;2]
% 2.86/0.96  --inst_dismatching                      true
% 2.86/0.96  --inst_eager_unprocessed_to_passive     true
% 2.86/0.96  --inst_prop_sim_given                   true
% 2.86/0.96  --inst_prop_sim_new                     false
% 2.86/0.96  --inst_subs_new                         false
% 2.86/0.96  --inst_eq_res_simp                      false
% 2.86/0.96  --inst_subs_given                       false
% 2.86/0.96  --inst_orphan_elimination               true
% 2.86/0.96  --inst_learning_loop_flag               true
% 2.86/0.96  --inst_learning_start                   3000
% 2.86/0.96  --inst_learning_factor                  2
% 2.86/0.96  --inst_start_prop_sim_after_learn       3
% 2.86/0.96  --inst_sel_renew                        solver
% 2.86/0.96  --inst_lit_activity_flag                true
% 2.86/0.96  --inst_restr_to_given                   false
% 2.86/0.96  --inst_activity_threshold               500
% 2.86/0.96  --inst_out_proof                        true
% 2.86/0.96  
% 2.86/0.96  ------ Resolution Options
% 2.86/0.96  
% 2.86/0.96  --resolution_flag                       false
% 2.86/0.96  --res_lit_sel                           adaptive
% 2.86/0.96  --res_lit_sel_side                      none
% 2.86/0.96  --res_ordering                          kbo
% 2.86/0.96  --res_to_prop_solver                    active
% 2.86/0.96  --res_prop_simpl_new                    false
% 2.86/0.96  --res_prop_simpl_given                  true
% 2.86/0.96  --res_passive_queue_type                priority_queues
% 2.86/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.86/0.96  --res_passive_queues_freq               [15;5]
% 2.86/0.96  --res_forward_subs                      full
% 2.86/0.96  --res_backward_subs                     full
% 2.86/0.96  --res_forward_subs_resolution           true
% 2.86/0.96  --res_backward_subs_resolution          true
% 2.86/0.96  --res_orphan_elimination                true
% 2.86/0.96  --res_time_limit                        2.
% 2.86/0.96  --res_out_proof                         true
% 2.86/0.96  
% 2.86/0.96  ------ Superposition Options
% 2.86/0.96  
% 2.86/0.96  --superposition_flag                    true
% 2.86/0.96  --sup_passive_queue_type                priority_queues
% 2.86/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.86/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.86/0.96  --demod_completeness_check              fast
% 2.86/0.96  --demod_use_ground                      true
% 2.86/0.96  --sup_to_prop_solver                    passive
% 2.86/0.96  --sup_prop_simpl_new                    true
% 2.86/0.96  --sup_prop_simpl_given                  true
% 2.86/0.96  --sup_fun_splitting                     false
% 2.86/0.96  --sup_smt_interval                      50000
% 2.86/0.96  
% 2.86/0.96  ------ Superposition Simplification Setup
% 2.86/0.96  
% 2.86/0.96  --sup_indices_passive                   []
% 2.86/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.86/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.96  --sup_full_bw                           [BwDemod]
% 2.86/0.96  --sup_immed_triv                        [TrivRules]
% 2.86/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.86/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.96  --sup_immed_bw_main                     []
% 2.86/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.86/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/0.96  
% 2.86/0.96  ------ Combination Options
% 2.86/0.96  
% 2.86/0.96  --comb_res_mult                         3
% 2.86/0.96  --comb_sup_mult                         2
% 2.86/0.96  --comb_inst_mult                        10
% 2.86/0.96  
% 2.86/0.96  ------ Debug Options
% 2.86/0.96  
% 2.86/0.96  --dbg_backtrace                         false
% 2.86/0.96  --dbg_dump_prop_clauses                 false
% 2.86/0.96  --dbg_dump_prop_clauses_file            -
% 2.86/0.96  --dbg_out_stat                          false
% 2.86/0.96  
% 2.86/0.96  
% 2.86/0.96  
% 2.86/0.96  
% 2.86/0.96  ------ Proving...
% 2.86/0.96  
% 2.86/0.96  
% 2.86/0.96  % SZS status Theorem for theBenchmark.p
% 2.86/0.96  
% 2.86/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.86/0.96  
% 2.86/0.96  fof(f16,conjecture,(
% 2.86/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 2.86/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.96  
% 2.86/0.96  fof(f17,negated_conjecture,(
% 2.86/0.96    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 2.86/0.96    inference(negated_conjecture,[],[f16])).
% 2.86/0.96  
% 2.86/0.96  fof(f37,plain,(
% 2.86/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.86/0.96    inference(ennf_transformation,[],[f17])).
% 2.86/0.96  
% 2.86/0.96  fof(f38,plain,(
% 2.86/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.86/0.96    inference(flattening,[],[f37])).
% 2.86/0.96  
% 2.86/0.96  fof(f47,plain,(
% 2.86/0.96    ( ! [X2,X0,X1] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 2.86/0.96    introduced(choice_axiom,[])).
% 2.86/0.96  
% 2.86/0.96  fof(f46,plain,(
% 2.86/0.96    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 2.86/0.96    introduced(choice_axiom,[])).
% 2.86/0.96  
% 2.86/0.96  fof(f45,plain,(
% 2.86/0.96    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.86/0.96    introduced(choice_axiom,[])).
% 2.86/0.96  
% 2.86/0.96  fof(f44,plain,(
% 2.86/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.86/0.96    introduced(choice_axiom,[])).
% 2.86/0.96  
% 2.86/0.96  fof(f48,plain,(
% 2.86/0.96    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.86/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f47,f46,f45,f44])).
% 2.86/0.96  
% 2.86/0.96  fof(f76,plain,(
% 2.86/0.96    m1_pre_topc(sK2,sK1)),
% 2.86/0.96    inference(cnf_transformation,[],[f48])).
% 2.86/0.96  
% 2.86/0.96  fof(f14,axiom,(
% 2.86/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.86/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.96  
% 2.86/0.96  fof(f35,plain,(
% 2.86/0.96    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.86/0.96    inference(ennf_transformation,[],[f14])).
% 2.86/0.96  
% 2.86/0.96  fof(f67,plain,(
% 2.86/0.96    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.86/0.96    inference(cnf_transformation,[],[f35])).
% 2.86/0.96  
% 2.86/0.96  fof(f2,axiom,(
% 2.86/0.96    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.86/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.96  
% 2.86/0.96  fof(f41,plain,(
% 2.86/0.96    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.86/0.96    inference(nnf_transformation,[],[f2])).
% 2.86/0.96  
% 2.86/0.96  fof(f52,plain,(
% 2.86/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.86/0.96    inference(cnf_transformation,[],[f41])).
% 2.86/0.96  
% 2.86/0.96  fof(f1,axiom,(
% 2.86/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.86/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.96  
% 2.86/0.96  fof(f39,plain,(
% 2.86/0.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.86/0.96    inference(nnf_transformation,[],[f1])).
% 2.86/0.96  
% 2.86/0.96  fof(f40,plain,(
% 2.86/0.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.86/0.96    inference(flattening,[],[f39])).
% 2.86/0.96  
% 2.86/0.96  fof(f51,plain,(
% 2.86/0.96    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.86/0.96    inference(cnf_transformation,[],[f40])).
% 2.86/0.96  
% 2.86/0.96  fof(f8,axiom,(
% 2.86/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.86/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.96  
% 2.86/0.96  fof(f26,plain,(
% 2.86/0.96    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.86/0.96    inference(ennf_transformation,[],[f8])).
% 2.86/0.96  
% 2.86/0.96  fof(f59,plain,(
% 2.86/0.96    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.86/0.96    inference(cnf_transformation,[],[f26])).
% 2.86/0.96  
% 2.86/0.96  fof(f74,plain,(
% 2.86/0.96    l1_pre_topc(sK1)),
% 2.86/0.96    inference(cnf_transformation,[],[f48])).
% 2.86/0.96  
% 2.86/0.96  fof(f15,axiom,(
% 2.86/0.96    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.86/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.96  
% 2.86/0.96  fof(f36,plain,(
% 2.86/0.96    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.86/0.96    inference(ennf_transformation,[],[f15])).
% 2.86/0.96  
% 2.86/0.96  fof(f68,plain,(
% 2.86/0.96    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.86/0.96    inference(cnf_transformation,[],[f36])).
% 2.86/0.96  
% 2.86/0.96  fof(f11,axiom,(
% 2.86/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.86/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.96  
% 2.86/0.96  fof(f30,plain,(
% 2.86/0.96    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.86/0.96    inference(ennf_transformation,[],[f11])).
% 2.86/0.96  
% 2.86/0.96  fof(f42,plain,(
% 2.86/0.96    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.86/0.96    inference(nnf_transformation,[],[f30])).
% 2.86/0.96  
% 2.86/0.96  fof(f62,plain,(
% 2.86/0.96    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.86/0.96    inference(cnf_transformation,[],[f42])).
% 2.86/0.96  
% 2.86/0.96  fof(f80,plain,(
% 2.86/0.96    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 2.86/0.96    inference(cnf_transformation,[],[f48])).
% 2.86/0.96  
% 2.86/0.96  fof(f10,axiom,(
% 2.86/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 2.86/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.96  
% 2.86/0.96  fof(f29,plain,(
% 2.86/0.96    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.86/0.96    inference(ennf_transformation,[],[f10])).
% 2.86/0.96  
% 2.86/0.96  fof(f61,plain,(
% 2.86/0.96    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 2.86/0.96    inference(cnf_transformation,[],[f29])).
% 2.86/0.96  
% 2.86/0.96  fof(f79,plain,(
% 2.86/0.96    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.86/0.96    inference(cnf_transformation,[],[f48])).
% 2.86/0.96  
% 2.86/0.96  fof(f13,axiom,(
% 2.86/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 2.86/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.96  
% 2.86/0.96  fof(f33,plain,(
% 2.86/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.86/0.96    inference(ennf_transformation,[],[f13])).
% 2.86/0.96  
% 2.86/0.96  fof(f34,plain,(
% 2.86/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.86/0.96    inference(flattening,[],[f33])).
% 2.86/0.96  
% 2.86/0.96  fof(f66,plain,(
% 2.86/0.96    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.86/0.96    inference(cnf_transformation,[],[f34])).
% 2.86/0.96  
% 2.86/0.96  fof(f77,plain,(
% 2.86/0.96    v1_funct_1(sK3)),
% 2.86/0.96    inference(cnf_transformation,[],[f48])).
% 2.86/0.96  
% 2.86/0.96  fof(f6,axiom,(
% 2.86/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 2.86/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.96  
% 2.86/0.96  fof(f23,plain,(
% 2.86/0.96    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.86/0.96    inference(ennf_transformation,[],[f6])).
% 2.86/0.96  
% 2.86/0.96  fof(f24,plain,(
% 2.86/0.96    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.86/0.96    inference(flattening,[],[f23])).
% 2.86/0.96  
% 2.86/0.96  fof(f57,plain,(
% 2.86/0.96    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.86/0.96    inference(cnf_transformation,[],[f24])).
% 2.86/0.96  
% 2.86/0.96  fof(f69,plain,(
% 2.86/0.96    ~v2_struct_0(sK0)),
% 2.86/0.96    inference(cnf_transformation,[],[f48])).
% 2.86/0.96  
% 2.86/0.96  fof(f70,plain,(
% 2.86/0.96    v2_pre_topc(sK0)),
% 2.86/0.96    inference(cnf_transformation,[],[f48])).
% 2.86/0.96  
% 2.86/0.96  fof(f71,plain,(
% 2.86/0.96    l1_pre_topc(sK0)),
% 2.86/0.96    inference(cnf_transformation,[],[f48])).
% 2.86/0.96  
% 2.86/0.96  fof(f72,plain,(
% 2.86/0.96    ~v2_struct_0(sK1)),
% 2.86/0.96    inference(cnf_transformation,[],[f48])).
% 2.86/0.96  
% 2.86/0.96  fof(f73,plain,(
% 2.86/0.96    v2_pre_topc(sK1)),
% 2.86/0.96    inference(cnf_transformation,[],[f48])).
% 2.86/0.96  
% 2.86/0.96  fof(f78,plain,(
% 2.86/0.96    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.86/0.96    inference(cnf_transformation,[],[f48])).
% 2.86/0.96  
% 2.86/0.96  fof(f7,axiom,(
% 2.86/0.96    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.86/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.96  
% 2.86/0.96  fof(f25,plain,(
% 2.86/0.96    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.86/0.96    inference(ennf_transformation,[],[f7])).
% 2.86/0.96  
% 2.86/0.96  fof(f58,plain,(
% 2.86/0.96    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.86/0.96    inference(cnf_transformation,[],[f25])).
% 2.86/0.96  
% 2.86/0.96  fof(f9,axiom,(
% 2.86/0.96    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.86/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.96  
% 2.86/0.96  fof(f27,plain,(
% 2.86/0.96    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.86/0.96    inference(ennf_transformation,[],[f9])).
% 2.86/0.96  
% 2.86/0.96  fof(f28,plain,(
% 2.86/0.96    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.86/0.96    inference(flattening,[],[f27])).
% 2.86/0.96  
% 2.86/0.96  fof(f60,plain,(
% 2.86/0.96    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.86/0.96    inference(cnf_transformation,[],[f28])).
% 2.86/0.96  
% 2.86/0.96  fof(f12,axiom,(
% 2.86/0.96    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 2.86/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.96  
% 2.86/0.96  fof(f31,plain,(
% 2.86/0.96    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.86/0.96    inference(ennf_transformation,[],[f12])).
% 2.86/0.96  
% 2.86/0.96  fof(f32,plain,(
% 2.86/0.96    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.86/0.96    inference(flattening,[],[f31])).
% 2.86/0.96  
% 2.86/0.96  fof(f43,plain,(
% 2.86/0.96    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.86/0.96    inference(nnf_transformation,[],[f32])).
% 2.86/0.96  
% 2.86/0.96  fof(f65,plain,(
% 2.86/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.86/0.96    inference(cnf_transformation,[],[f43])).
% 2.86/0.96  
% 2.86/0.96  fof(f84,plain,(
% 2.86/0.96    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.86/0.96    inference(equality_resolution,[],[f65])).
% 2.86/0.96  
% 2.86/0.96  fof(f81,plain,(
% 2.86/0.96    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 2.86/0.96    inference(cnf_transformation,[],[f48])).
% 2.86/0.96  
% 2.86/0.96  fof(f5,axiom,(
% 2.86/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.86/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.96  
% 2.86/0.96  fof(f18,plain,(
% 2.86/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.86/0.96    inference(pure_predicate_removal,[],[f5])).
% 2.86/0.96  
% 2.86/0.96  fof(f22,plain,(
% 2.86/0.96    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/0.96    inference(ennf_transformation,[],[f18])).
% 2.86/0.96  
% 2.86/0.96  fof(f56,plain,(
% 2.86/0.96    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/0.96    inference(cnf_transformation,[],[f22])).
% 2.86/0.96  
% 2.86/0.96  fof(f3,axiom,(
% 2.86/0.96    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.86/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.96  
% 2.86/0.96  fof(f19,plain,(
% 2.86/0.96    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.86/0.96    inference(ennf_transformation,[],[f3])).
% 2.86/0.96  
% 2.86/0.96  fof(f20,plain,(
% 2.86/0.96    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.86/0.96    inference(flattening,[],[f19])).
% 2.86/0.96  
% 2.86/0.96  fof(f54,plain,(
% 2.86/0.96    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.86/0.96    inference(cnf_transformation,[],[f20])).
% 2.86/0.96  
% 2.86/0.96  fof(f4,axiom,(
% 2.86/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.86/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.96  
% 2.86/0.96  fof(f21,plain,(
% 2.86/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/0.96    inference(ennf_transformation,[],[f4])).
% 2.86/0.96  
% 2.86/0.96  fof(f55,plain,(
% 2.86/0.96    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/0.96    inference(cnf_transformation,[],[f21])).
% 2.86/0.96  
% 2.86/0.96  cnf(c_25,negated_conjecture,
% 2.86/0.96      ( m1_pre_topc(sK2,sK1) ),
% 2.86/0.96      inference(cnf_transformation,[],[f76]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_1480,plain,
% 2.86/0.96      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_18,plain,
% 2.86/0.96      ( ~ m1_pre_topc(X0,X1)
% 2.86/0.96      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.86/0.96      | ~ l1_pre_topc(X1) ),
% 2.86/0.96      inference(cnf_transformation,[],[f67]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_1484,plain,
% 2.86/0.96      ( m1_pre_topc(X0,X1) != iProver_top
% 2.86/0.96      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 2.86/0.96      | l1_pre_topc(X1) != iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_4,plain,
% 2.86/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.86/0.96      inference(cnf_transformation,[],[f52]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_1487,plain,
% 2.86/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.86/0.96      | r1_tarski(X0,X1) = iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_3014,plain,
% 2.86/0.96      ( m1_pre_topc(X0,X1) != iProver_top
% 2.86/0.96      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 2.86/0.96      | l1_pre_topc(X1) != iProver_top ),
% 2.86/0.96      inference(superposition,[status(thm)],[c_1484,c_1487]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_0,plain,
% 2.86/0.96      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.86/0.96      inference(cnf_transformation,[],[f51]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_1490,plain,
% 2.86/0.96      ( X0 = X1
% 2.86/0.96      | r1_tarski(X0,X1) != iProver_top
% 2.86/0.96      | r1_tarski(X1,X0) != iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_3595,plain,
% 2.86/0.96      ( u1_struct_0(X0) = u1_struct_0(X1)
% 2.86/0.96      | m1_pre_topc(X1,X0) != iProver_top
% 2.86/0.96      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 2.86/0.96      | l1_pre_topc(X0) != iProver_top ),
% 2.86/0.96      inference(superposition,[status(thm)],[c_3014,c_1490]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_3800,plain,
% 2.86/0.96      ( u1_struct_0(X0) = u1_struct_0(X1)
% 2.86/0.96      | m1_pre_topc(X1,X0) != iProver_top
% 2.86/0.96      | m1_pre_topc(X0,X1) != iProver_top
% 2.86/0.96      | l1_pre_topc(X1) != iProver_top
% 2.86/0.96      | l1_pre_topc(X0) != iProver_top ),
% 2.86/0.96      inference(superposition,[status(thm)],[c_3014,c_3595]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_10,plain,
% 2.86/0.96      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.86/0.96      inference(cnf_transformation,[],[f59]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_68,plain,
% 2.86/0.96      ( m1_pre_topc(X0,X1) != iProver_top
% 2.86/0.96      | l1_pre_topc(X1) != iProver_top
% 2.86/0.96      | l1_pre_topc(X0) = iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_4287,plain,
% 2.86/0.96      ( l1_pre_topc(X1) != iProver_top
% 2.86/0.96      | m1_pre_topc(X0,X1) != iProver_top
% 2.86/0.96      | m1_pre_topc(X1,X0) != iProver_top
% 2.86/0.96      | u1_struct_0(X0) = u1_struct_0(X1) ),
% 2.86/0.96      inference(global_propositional_subsumption,
% 2.86/0.96                [status(thm)],
% 2.86/0.96                [c_3800,c_68,c_3014,c_3595]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_4288,plain,
% 2.86/0.96      ( u1_struct_0(X0) = u1_struct_0(X1)
% 2.86/0.96      | m1_pre_topc(X0,X1) != iProver_top
% 2.86/0.96      | m1_pre_topc(X1,X0) != iProver_top
% 2.86/0.96      | l1_pre_topc(X1) != iProver_top ),
% 2.86/0.96      inference(renaming,[status(thm)],[c_4287]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_4297,plain,
% 2.86/0.96      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 2.86/0.96      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.86/0.96      | l1_pre_topc(sK1) != iProver_top ),
% 2.86/0.96      inference(superposition,[status(thm)],[c_1480,c_4288]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_27,negated_conjecture,
% 2.86/0.96      ( l1_pre_topc(sK1) ),
% 2.86/0.96      inference(cnf_transformation,[],[f74]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_38,plain,
% 2.86/0.96      ( l1_pre_topc(sK1) = iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_19,plain,
% 2.86/0.96      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.86/0.96      inference(cnf_transformation,[],[f68]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_45,plain,
% 2.86/0.96      ( m1_pre_topc(X0,X0) = iProver_top
% 2.86/0.96      | l1_pre_topc(X0) != iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_47,plain,
% 2.86/0.96      ( m1_pre_topc(sK1,sK1) = iProver_top
% 2.86/0.96      | l1_pre_topc(sK1) != iProver_top ),
% 2.86/0.96      inference(instantiation,[status(thm)],[c_45]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_14,plain,
% 2.86/0.96      ( ~ m1_pre_topc(X0,X1)
% 2.86/0.96      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.86/0.96      | ~ l1_pre_topc(X0)
% 2.86/0.96      | ~ l1_pre_topc(X1) ),
% 2.86/0.96      inference(cnf_transformation,[],[f62]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_60,plain,
% 2.86/0.96      ( m1_pre_topc(X0,X1) != iProver_top
% 2.86/0.96      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 2.86/0.96      | l1_pre_topc(X0) != iProver_top
% 2.86/0.96      | l1_pre_topc(X1) != iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_62,plain,
% 2.86/0.96      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.86/0.96      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.86/0.96      | l1_pre_topc(sK1) != iProver_top ),
% 2.86/0.96      inference(instantiation,[status(thm)],[c_60]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_1486,plain,
% 2.86/0.96      ( m1_pre_topc(X0,X1) != iProver_top
% 2.86/0.96      | l1_pre_topc(X1) != iProver_top
% 2.86/0.96      | l1_pre_topc(X0) = iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_2457,plain,
% 2.86/0.96      ( l1_pre_topc(sK2) = iProver_top
% 2.86/0.96      | l1_pre_topc(sK1) != iProver_top ),
% 2.86/0.96      inference(superposition,[status(thm)],[c_1480,c_1486]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_21,negated_conjecture,
% 2.86/0.96      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 2.86/0.96      inference(cnf_transformation,[],[f80]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_12,plain,
% 2.86/0.96      ( m1_pre_topc(X0,X1)
% 2.86/0.96      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.86/0.96      | ~ l1_pre_topc(X1) ),
% 2.86/0.96      inference(cnf_transformation,[],[f61]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_1485,plain,
% 2.86/0.96      ( m1_pre_topc(X0,X1) = iProver_top
% 2.86/0.96      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 2.86/0.96      | l1_pre_topc(X1) != iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_3024,plain,
% 2.86/0.96      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.86/0.96      | m1_pre_topc(X0,sK2) = iProver_top
% 2.86/0.96      | l1_pre_topc(sK2) != iProver_top ),
% 2.86/0.96      inference(superposition,[status(thm)],[c_21,c_1485]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_3041,plain,
% 2.86/0.96      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.86/0.96      | m1_pre_topc(sK1,sK2) = iProver_top
% 2.86/0.96      | l1_pre_topc(sK2) != iProver_top ),
% 2.86/0.96      inference(instantiation,[status(thm)],[c_3024]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_4573,plain,
% 2.86/0.96      ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 2.86/0.96      inference(global_propositional_subsumption,
% 2.86/0.96                [status(thm)],
% 2.86/0.96                [c_4297,c_38,c_47,c_62,c_2457,c_3041]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_22,negated_conjecture,
% 2.86/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 2.86/0.96      inference(cnf_transformation,[],[f79]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_1482,plain,
% 2.86/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_17,plain,
% 2.86/0.96      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.86/0.96      | ~ m1_pre_topc(X3,X1)
% 2.86/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.86/0.96      | ~ v2_pre_topc(X2)
% 2.86/0.96      | ~ v2_pre_topc(X1)
% 2.86/0.96      | v2_struct_0(X1)
% 2.86/0.96      | v2_struct_0(X2)
% 2.86/0.96      | ~ l1_pre_topc(X1)
% 2.86/0.96      | ~ l1_pre_topc(X2)
% 2.86/0.96      | ~ v1_funct_1(X0)
% 2.86/0.96      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.86/0.96      inference(cnf_transformation,[],[f66]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_24,negated_conjecture,
% 2.86/0.96      ( v1_funct_1(sK3) ),
% 2.86/0.96      inference(cnf_transformation,[],[f77]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_530,plain,
% 2.86/0.96      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.86/0.96      | ~ m1_pre_topc(X3,X1)
% 2.86/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.86/0.96      | ~ v2_pre_topc(X1)
% 2.86/0.96      | ~ v2_pre_topc(X2)
% 2.86/0.96      | v2_struct_0(X1)
% 2.86/0.96      | v2_struct_0(X2)
% 2.86/0.96      | ~ l1_pre_topc(X1)
% 2.86/0.96      | ~ l1_pre_topc(X2)
% 2.86/0.96      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 2.86/0.96      | sK3 != X0 ),
% 2.86/0.96      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_531,plain,
% 2.86/0.96      ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
% 2.86/0.96      | ~ m1_pre_topc(X2,X0)
% 2.86/0.96      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.86/0.96      | ~ v2_pre_topc(X0)
% 2.86/0.96      | ~ v2_pre_topc(X1)
% 2.86/0.96      | v2_struct_0(X0)
% 2.86/0.96      | v2_struct_0(X1)
% 2.86/0.96      | ~ l1_pre_topc(X0)
% 2.86/0.96      | ~ l1_pre_topc(X1)
% 2.86/0.96      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2) ),
% 2.86/0.96      inference(unflattening,[status(thm)],[c_530]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_1470,plain,
% 2.86/0.96      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2)
% 2.86/0.96      | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 2.86/0.96      | m1_pre_topc(X2,X0) != iProver_top
% 2.86/0.96      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.86/0.96      | v2_pre_topc(X1) != iProver_top
% 2.86/0.96      | v2_pre_topc(X0) != iProver_top
% 2.86/0.96      | v2_struct_0(X1) = iProver_top
% 2.86/0.96      | v2_struct_0(X0) = iProver_top
% 2.86/0.96      | l1_pre_topc(X0) != iProver_top
% 2.86/0.96      | l1_pre_topc(X1) != iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_2074,plain,
% 2.86/0.96      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 2.86/0.96      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.86/0.96      | m1_pre_topc(X0,sK1) != iProver_top
% 2.86/0.96      | v2_pre_topc(sK0) != iProver_top
% 2.86/0.96      | v2_pre_topc(sK1) != iProver_top
% 2.86/0.96      | v2_struct_0(sK0) = iProver_top
% 2.86/0.96      | v2_struct_0(sK1) = iProver_top
% 2.86/0.96      | l1_pre_topc(sK0) != iProver_top
% 2.86/0.96      | l1_pre_topc(sK1) != iProver_top ),
% 2.86/0.96      inference(superposition,[status(thm)],[c_1482,c_1470]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_8,plain,
% 2.86/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/0.96      | ~ v1_funct_1(X0)
% 2.86/0.96      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.86/0.96      inference(cnf_transformation,[],[f57]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_566,plain,
% 2.86/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/0.96      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 2.86/0.96      | sK3 != X0 ),
% 2.86/0.96      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_567,plain,
% 2.86/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.86/0.96      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 2.86/0.96      inference(unflattening,[status(thm)],[c_566]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_1469,plain,
% 2.86/0.96      ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 2.86/0.96      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_567]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_1903,plain,
% 2.86/0.96      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
% 2.86/0.96      inference(superposition,[status(thm)],[c_1482,c_1469]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_2075,plain,
% 2.86/0.96      ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
% 2.86/0.96      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.86/0.96      | m1_pre_topc(X0,sK1) != iProver_top
% 2.86/0.96      | v2_pre_topc(sK0) != iProver_top
% 2.86/0.96      | v2_pre_topc(sK1) != iProver_top
% 2.86/0.96      | v2_struct_0(sK0) = iProver_top
% 2.86/0.96      | v2_struct_0(sK1) = iProver_top
% 2.86/0.96      | l1_pre_topc(sK0) != iProver_top
% 2.86/0.96      | l1_pre_topc(sK1) != iProver_top ),
% 2.86/0.96      inference(demodulation,[status(thm)],[c_2074,c_1903]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_32,negated_conjecture,
% 2.86/0.96      ( ~ v2_struct_0(sK0) ),
% 2.86/0.96      inference(cnf_transformation,[],[f69]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_33,plain,
% 2.86/0.96      ( v2_struct_0(sK0) != iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_31,negated_conjecture,
% 2.86/0.96      ( v2_pre_topc(sK0) ),
% 2.86/0.96      inference(cnf_transformation,[],[f70]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_34,plain,
% 2.86/0.96      ( v2_pre_topc(sK0) = iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_30,negated_conjecture,
% 2.86/0.96      ( l1_pre_topc(sK0) ),
% 2.86/0.96      inference(cnf_transformation,[],[f71]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_35,plain,
% 2.86/0.96      ( l1_pre_topc(sK0) = iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_29,negated_conjecture,
% 2.86/0.96      ( ~ v2_struct_0(sK1) ),
% 2.86/0.96      inference(cnf_transformation,[],[f72]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_36,plain,
% 2.86/0.96      ( v2_struct_0(sK1) != iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_28,negated_conjecture,
% 2.86/0.96      ( v2_pre_topc(sK1) ),
% 2.86/0.96      inference(cnf_transformation,[],[f73]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_37,plain,
% 2.86/0.96      ( v2_pre_topc(sK1) = iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_23,negated_conjecture,
% 2.86/0.96      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 2.86/0.96      inference(cnf_transformation,[],[f78]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_42,plain,
% 2.86/0.96      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_2161,plain,
% 2.86/0.96      ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
% 2.86/0.96      | m1_pre_topc(X0,sK1) != iProver_top ),
% 2.86/0.96      inference(global_propositional_subsumption,
% 2.86/0.96                [status(thm)],
% 2.86/0.96                [c_2075,c_33,c_34,c_35,c_36,c_37,c_38,c_42]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_2169,plain,
% 2.86/0.96      ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 2.86/0.96      inference(superposition,[status(thm)],[c_1480,c_2161]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_9,plain,
% 2.86/0.96      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.86/0.96      inference(cnf_transformation,[],[f58]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_11,plain,
% 2.86/0.96      ( v2_struct_0(X0)
% 2.86/0.96      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.86/0.96      | ~ l1_struct_0(X0) ),
% 2.86/0.96      inference(cnf_transformation,[],[f60]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_435,plain,
% 2.86/0.96      ( v2_struct_0(X0)
% 2.86/0.96      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.86/0.96      | ~ l1_pre_topc(X0) ),
% 2.86/0.96      inference(resolution,[status(thm)],[c_9,c_11]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_15,plain,
% 2.86/0.96      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 2.86/0.96      | ~ v1_funct_2(X4,X2,X3)
% 2.86/0.96      | ~ v1_funct_2(X4,X0,X1)
% 2.86/0.96      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.86/0.96      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.86/0.96      | v1_xboole_0(X1)
% 2.86/0.96      | v1_xboole_0(X3)
% 2.86/0.96      | ~ v1_funct_1(X4) ),
% 2.86/0.96      inference(cnf_transformation,[],[f84]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_20,negated_conjecture,
% 2.86/0.96      ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
% 2.86/0.96      inference(cnf_transformation,[],[f81]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_455,plain,
% 2.86/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 2.86/0.96      | ~ v1_funct_2(X0,X3,X4)
% 2.86/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.86/0.96      | v1_xboole_0(X4)
% 2.86/0.96      | v1_xboole_0(X2)
% 2.86/0.96      | ~ v1_funct_1(X0)
% 2.86/0.96      | k2_tmap_1(sK1,sK0,sK3,sK2) != X0
% 2.86/0.96      | u1_struct_0(sK2) != X1
% 2.86/0.96      | u1_struct_0(sK0) != X2
% 2.86/0.96      | u1_struct_0(sK0) != X4
% 2.86/0.96      | u1_struct_0(sK1) != X3
% 2.86/0.96      | sK3 != X0 ),
% 2.86/0.96      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_456,plain,
% 2.86/0.96      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.86/0.96      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.86/0.96      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.86/0.96      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.86/0.96      | v1_xboole_0(u1_struct_0(sK0))
% 2.86/0.96      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 2.86/0.96      | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 2.86/0.96      inference(unflattening,[status(thm)],[c_455]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_488,plain,
% 2.86/0.96      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.86/0.96      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.86/0.96      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.86/0.96      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.86/0.96      | v2_struct_0(X0)
% 2.86/0.96      | ~ l1_pre_topc(X0)
% 2.86/0.96      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 2.86/0.96      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 2.86/0.96      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 2.86/0.96      inference(resolution_lifted,[status(thm)],[c_435,c_456]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_578,plain,
% 2.86/0.96      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.86/0.96      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.86/0.96      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.86/0.96      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.86/0.96      | v2_struct_0(X0)
% 2.86/0.96      | ~ l1_pre_topc(X0)
% 2.86/0.96      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 2.86/0.96      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 2.86/0.96      inference(resolution_lifted,[status(thm)],[c_24,c_488]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_842,plain,
% 2.86/0.96      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.86/0.96      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.86/0.96      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.86/0.96      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.86/0.96      | sP0_iProver_split
% 2.86/0.96      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
% 2.86/0.96      inference(splitting,
% 2.86/0.96                [splitting(split),new_symbols(definition,[])],
% 2.86/0.96                [c_578]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_1467,plain,
% 2.86/0.96      ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 2.86/0.96      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.86/0.96      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.86/0.96      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.86/0.96      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.86/0.96      | sP0_iProver_split = iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_842]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_2171,plain,
% 2.86/0.96      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 2.86/0.96      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.86/0.96      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.86/0.96      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.86/0.96      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.86/0.96      | sP0_iProver_split = iProver_top ),
% 2.86/0.96      inference(demodulation,[status(thm)],[c_2169,c_1467]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_841,plain,
% 2.86/0.96      ( v2_struct_0(X0)
% 2.86/0.96      | ~ l1_pre_topc(X0)
% 2.86/0.96      | u1_struct_0(X0) != u1_struct_0(sK0)
% 2.86/0.96      | ~ sP0_iProver_split ),
% 2.86/0.96      inference(splitting,
% 2.86/0.96                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.86/0.96                [c_578]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_1468,plain,
% 2.86/0.96      ( u1_struct_0(X0) != u1_struct_0(sK0)
% 2.86/0.96      | v2_struct_0(X0) = iProver_top
% 2.86/0.96      | l1_pre_topc(X0) != iProver_top
% 2.86/0.96      | sP0_iProver_split != iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_841]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_1986,plain,
% 2.86/0.96      ( v2_struct_0(sK0) = iProver_top
% 2.86/0.96      | l1_pre_topc(sK0) != iProver_top
% 2.86/0.96      | sP0_iProver_split != iProver_top ),
% 2.86/0.96      inference(equality_resolution,[status(thm)],[c_1468]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_2243,plain,
% 2.86/0.96      ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.86/0.96      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.86/0.96      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.86/0.96      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.86/0.96      | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
% 2.86/0.96      inference(global_propositional_subsumption,
% 2.86/0.96                [status(thm)],
% 2.86/0.96                [c_2171,c_33,c_35,c_1986]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_2244,plain,
% 2.86/0.96      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 2.86/0.96      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.86/0.96      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.86/0.96      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.86/0.96      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.86/0.96      inference(renaming,[status(thm)],[c_2243]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_4576,plain,
% 2.86/0.96      ( k7_relat_1(sK3,u1_struct_0(sK1)) != sK3
% 2.86/0.96      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.86/0.96      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.86/0.96      inference(demodulation,[status(thm)],[c_4573,c_2244]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_7,plain,
% 2.86/0.96      ( v4_relat_1(X0,X1)
% 2.86/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.86/0.96      inference(cnf_transformation,[],[f56]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_5,plain,
% 2.86/0.96      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.86/0.96      inference(cnf_transformation,[],[f54]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_415,plain,
% 2.86/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/0.96      | ~ v1_relat_1(X0)
% 2.86/0.96      | k7_relat_1(X0,X1) = X0 ),
% 2.86/0.96      inference(resolution,[status(thm)],[c_7,c_5]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_6,plain,
% 2.86/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/0.96      | v1_relat_1(X0) ),
% 2.86/0.96      inference(cnf_transformation,[],[f55]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_419,plain,
% 2.86/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/0.96      | k7_relat_1(X0,X1) = X0 ),
% 2.86/0.96      inference(global_propositional_subsumption,
% 2.86/0.96                [status(thm)],
% 2.86/0.96                [c_415,c_7,c_6,c_5]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_1471,plain,
% 2.86/0.96      ( k7_relat_1(X0,X1) = X0
% 2.86/0.96      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_2255,plain,
% 2.86/0.96      ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
% 2.86/0.96      inference(superposition,[status(thm)],[c_1482,c_1471]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_4587,plain,
% 2.86/0.96      ( sK3 != sK3
% 2.86/0.96      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.86/0.96      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.86/0.96      inference(light_normalisation,[status(thm)],[c_4576,c_2255]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_4588,plain,
% 2.86/0.96      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.86/0.96      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.86/0.96      inference(equality_resolution_simp,[status(thm)],[c_4587]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(c_43,plain,
% 2.86/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 2.86/0.96      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.86/0.96  
% 2.86/0.96  cnf(contradiction,plain,
% 2.86/0.96      ( $false ),
% 2.86/0.96      inference(minisat,[status(thm)],[c_4588,c_43,c_42]) ).
% 2.86/0.96  
% 2.86/0.96  
% 2.86/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 2.86/0.96  
% 2.86/0.96  ------                               Statistics
% 2.86/0.96  
% 2.86/0.96  ------ General
% 2.86/0.96  
% 2.86/0.96  abstr_ref_over_cycles:                  0
% 2.86/0.96  abstr_ref_under_cycles:                 0
% 2.86/0.96  gc_basic_clause_elim:                   0
% 2.86/0.96  forced_gc_time:                         0
% 2.86/0.96  parsing_time:                           0.025
% 2.86/0.96  unif_index_cands_time:                  0.
% 2.86/0.96  unif_index_add_time:                    0.
% 2.86/0.96  orderings_time:                         0.
% 2.86/0.96  out_proof_time:                         0.01
% 2.86/0.96  total_time:                             0.173
% 2.86/0.96  num_of_symbols:                         57
% 2.86/0.96  num_of_terms:                           3030
% 2.86/0.96  
% 2.86/0.96  ------ Preprocessing
% 2.86/0.96  
% 2.86/0.96  num_of_splits:                          1
% 2.86/0.96  num_of_split_atoms:                     1
% 2.86/0.96  num_of_reused_defs:                     0
% 2.86/0.96  num_eq_ax_congr_red:                    15
% 2.86/0.96  num_of_sem_filtered_clauses:            1
% 2.86/0.96  num_of_subtypes:                        0
% 2.86/0.96  monotx_restored_types:                  0
% 2.86/0.96  sat_num_of_epr_types:                   0
% 2.86/0.96  sat_num_of_non_cyclic_types:            0
% 2.86/0.96  sat_guarded_non_collapsed_types:        0
% 2.86/0.96  num_pure_diseq_elim:                    0
% 2.86/0.96  simp_replaced_by:                       0
% 2.86/0.96  res_preprocessed:                       138
% 2.86/0.96  prep_upred:                             0
% 2.86/0.96  prep_unflattend:                        13
% 2.86/0.96  smt_new_axioms:                         0
% 2.86/0.96  pred_elim_cands:                        7
% 2.86/0.96  pred_elim:                              6
% 2.86/0.96  pred_elim_cl:                           7
% 2.86/0.96  pred_elim_cycles:                       8
% 2.86/0.96  merged_defs:                            8
% 2.86/0.96  merged_defs_ncl:                        0
% 2.86/0.96  bin_hyper_res:                          8
% 2.86/0.96  prep_cycles:                            4
% 2.86/0.96  pred_elim_time:                         0.006
% 2.86/0.96  splitting_time:                         0.
% 2.86/0.96  sem_filter_time:                        0.
% 2.86/0.96  monotx_time:                            0.
% 2.86/0.96  subtype_inf_time:                       0.
% 2.86/0.96  
% 2.86/0.96  ------ Problem properties
% 2.86/0.96  
% 2.86/0.96  clauses:                                25
% 2.86/0.96  conjectures:                            11
% 2.86/0.96  epr:                                    12
% 2.86/0.96  horn:                                   24
% 2.86/0.96  ground:                                 12
% 2.86/0.96  unary:                                  12
% 2.86/0.96  binary:                                 5
% 2.86/0.96  lits:                                   57
% 2.86/0.96  lits_eq:                                7
% 2.86/0.96  fd_pure:                                0
% 2.86/0.96  fd_pseudo:                              0
% 2.86/0.96  fd_cond:                                0
% 2.86/0.96  fd_pseudo_cond:                         1
% 2.86/0.96  ac_symbols:                             0
% 2.86/0.96  
% 2.86/0.96  ------ Propositional Solver
% 2.86/0.96  
% 2.86/0.96  prop_solver_calls:                      29
% 2.86/0.96  prop_fast_solver_calls:                 947
% 2.86/0.96  smt_solver_calls:                       0
% 2.86/0.96  smt_fast_solver_calls:                  0
% 2.86/0.96  prop_num_of_clauses:                    1265
% 2.86/0.96  prop_preprocess_simplified:             4953
% 2.86/0.96  prop_fo_subsumed:                       24
% 2.86/0.96  prop_solver_time:                       0.
% 2.86/0.96  smt_solver_time:                        0.
% 2.86/0.96  smt_fast_solver_time:                   0.
% 2.86/0.96  prop_fast_solver_time:                  0.
% 2.86/0.96  prop_unsat_core_time:                   0.
% 2.86/0.96  
% 2.86/0.96  ------ QBF
% 2.86/0.96  
% 2.86/0.96  qbf_q_res:                              0
% 2.86/0.96  qbf_num_tautologies:                    0
% 2.86/0.96  qbf_prep_cycles:                        0
% 2.86/0.96  
% 2.86/0.96  ------ BMC1
% 2.86/0.96  
% 2.86/0.96  bmc1_current_bound:                     -1
% 2.86/0.96  bmc1_last_solved_bound:                 -1
% 2.86/0.96  bmc1_unsat_core_size:                   -1
% 2.86/0.96  bmc1_unsat_core_parents_size:           -1
% 2.86/0.96  bmc1_merge_next_fun:                    0
% 2.86/0.96  bmc1_unsat_core_clauses_time:           0.
% 2.86/0.96  
% 2.86/0.96  ------ Instantiation
% 2.86/0.96  
% 2.86/0.96  inst_num_of_clauses:                    446
% 2.86/0.96  inst_num_in_passive:                    48
% 2.86/0.96  inst_num_in_active:                     294
% 2.86/0.96  inst_num_in_unprocessed:                105
% 2.86/0.96  inst_num_of_loops:                      310
% 2.86/0.96  inst_num_of_learning_restarts:          0
% 2.86/0.96  inst_num_moves_active_passive:          11
% 2.86/0.96  inst_lit_activity:                      0
% 2.86/0.96  inst_lit_activity_moves:                0
% 2.86/0.96  inst_num_tautologies:                   0
% 2.86/0.96  inst_num_prop_implied:                  0
% 2.86/0.96  inst_num_existing_simplified:           0
% 2.86/0.96  inst_num_eq_res_simplified:             0
% 2.86/0.96  inst_num_child_elim:                    0
% 2.86/0.96  inst_num_of_dismatching_blockings:      214
% 2.86/0.96  inst_num_of_non_proper_insts:           723
% 2.86/0.96  inst_num_of_duplicates:                 0
% 2.86/0.96  inst_inst_num_from_inst_to_res:         0
% 2.86/0.96  inst_dismatching_checking_time:         0.
% 2.86/0.96  
% 2.86/0.96  ------ Resolution
% 2.86/0.96  
% 2.86/0.96  res_num_of_clauses:                     0
% 2.86/0.96  res_num_in_passive:                     0
% 2.86/0.96  res_num_in_active:                      0
% 2.86/0.96  res_num_of_loops:                       142
% 2.86/0.96  res_forward_subset_subsumed:            111
% 2.86/0.96  res_backward_subset_subsumed:           4
% 2.86/0.96  res_forward_subsumed:                   0
% 2.86/0.96  res_backward_subsumed:                  0
% 2.86/0.96  res_forward_subsumption_resolution:     0
% 2.86/0.96  res_backward_subsumption_resolution:    0
% 2.86/0.96  res_clause_to_clause_subsumption:       285
% 2.86/0.96  res_orphan_elimination:                 0
% 2.86/0.96  res_tautology_del:                      112
% 2.86/0.96  res_num_eq_res_simplified:              0
% 2.86/0.96  res_num_sel_changes:                    0
% 2.86/0.96  res_moves_from_active_to_pass:          0
% 2.86/0.96  
% 2.86/0.96  ------ Superposition
% 2.86/0.96  
% 2.86/0.96  sup_time_total:                         0.
% 2.86/0.96  sup_time_generating:                    0.
% 2.86/0.96  sup_time_sim_full:                      0.
% 2.86/0.96  sup_time_sim_immed:                     0.
% 2.86/0.96  
% 2.86/0.96  sup_num_of_clauses:                     70
% 2.86/0.96  sup_num_in_active:                      56
% 2.86/0.96  sup_num_in_passive:                     14
% 2.86/0.96  sup_num_of_loops:                       60
% 2.86/0.96  sup_fw_superposition:                   43
% 2.86/0.96  sup_bw_superposition:                   44
% 2.86/0.96  sup_immediate_simplified:               16
% 2.86/0.96  sup_given_eliminated:                   0
% 2.86/0.96  comparisons_done:                       0
% 2.86/0.96  comparisons_avoided:                    0
% 2.86/0.96  
% 2.86/0.96  ------ Simplifications
% 2.86/0.96  
% 2.86/0.96  
% 2.86/0.96  sim_fw_subset_subsumed:                 7
% 2.86/0.96  sim_bw_subset_subsumed:                 3
% 2.86/0.96  sim_fw_subsumed:                        1
% 2.86/0.96  sim_bw_subsumed:                        2
% 2.86/0.96  sim_fw_subsumption_res:                 0
% 2.86/0.96  sim_bw_subsumption_res:                 0
% 2.86/0.96  sim_tautology_del:                      14
% 2.86/0.96  sim_eq_tautology_del:                   5
% 2.86/0.96  sim_eq_res_simp:                        1
% 2.86/0.96  sim_fw_demodulated:                     1
% 2.86/0.96  sim_bw_demodulated:                     4
% 2.86/0.96  sim_light_normalised:                   7
% 2.86/0.96  sim_joinable_taut:                      0
% 2.86/0.96  sim_joinable_simp:                      0
% 2.86/0.96  sim_ac_normalised:                      0
% 2.86/0.96  sim_smt_subsumption:                    0
% 2.86/0.96  
%------------------------------------------------------------------------------
