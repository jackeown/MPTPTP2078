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
% DateTime   : Thu Dec  3 12:22:30 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 690 expanded)
%              Number of clauses        :  106 ( 205 expanded)
%              Number of leaves         :   19 ( 214 expanded)
%              Depth                    :   25
%              Number of atoms          :  733 (5861 expanded)
%              Number of equality atoms :  235 ( 802 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f46,f45,f44,f43])).

fof(f76,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f68,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f80,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

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
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f30])).

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
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f47])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1477,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1482,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1488,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2512,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1482,c_1488])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1491,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2893,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2512,c_1491])).

cnf(c_4144,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2512,c_2893])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_69,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6409,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4144,c_69,c_2512,c_2893])).

cnf(c_6410,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6409])).

cnf(c_6419,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_pre_topc(sK1,sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1477,c_6410])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_39,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_20,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_46,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_48,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_61,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_63,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_1485,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2357,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1477,c_1485])).

cnf(c_22,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_13,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1484,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2618,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1484])).

cnf(c_2635,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2618])).

cnf(c_6606,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6419,c_39,c_48,c_63,c_2357,c_2635])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1489,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1481,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_185,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_11])).

cnf(c_186,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_185])).

cnf(c_1469,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_2638,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2618,c_39,c_2357])).

cnf(c_2639,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_2638])).

cnf(c_3039,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1469,c_2639])).

cnf(c_3480,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3039,c_39])).

cnf(c_3481,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3480])).

cnf(c_3488,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_3481])).

cnf(c_3989,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3488,c_39,c_48,c_63,c_2357,c_2635])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1480,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_9,plain,
    ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3),X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(X0,X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_451,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X1,X7)
    | ~ v1_funct_1(X0)
    | X0 != X6
    | X2 != X5
    | X1 != X4
    | X6 = X3
    | k2_partfun1(X1,X2,X0,X7) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_9])).

cnf(c_452,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X1,X3)
    | ~ v1_funct_1(X0)
    | X0 = k2_partfun1(X1,X2,X0,X3) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ v1_funct_1(X0)
    | X0 = k2_partfun1(X1,X2,X0,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_7])).

cnf(c_457,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X1,X3)
    | ~ v1_funct_1(X0)
    | X0 = k2_partfun1(X1,X2,X0,X3) ),
    inference(renaming,[status(thm)],[c_456])).

cnf(c_1468,plain,
    ( X0 = k2_partfun1(X1,X2,X0,X3)
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(X1,X3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_2327,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = sK3
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(u1_struct_0(sK1),X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_1468])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_42,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_43,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2800,plain,
    ( r1_tarski(u1_struct_0(sK1),X0) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2327,c_42,c_43])).

cnf(c_2801,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = sK3
    | r1_tarski(u1_struct_0(sK1),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2800])).

cnf(c_2894,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = sK3
    | m1_pre_topc(sK1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2512,c_2801])).

cnf(c_4396,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK3
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3989,c_2894])).

cnf(c_18,plain,
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

cnf(c_1483,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3333,plain,
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
    inference(superposition,[status(thm)],[c_1480,c_1483])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_34,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_35,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_36,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_37,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_38,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3726,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3333,c_34,c_35,c_36,c_37,c_38,c_39,c_42,c_43])).

cnf(c_3727,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3726])).

cnf(c_3735,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1477,c_3727])).

cnf(c_4399,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = sK3
    | l1_pre_topc(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4396,c_3735])).

cnf(c_4570,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4399,c_39,c_2357])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_12,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_431,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_10,c_12])).

cnf(c_16,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_21,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_486,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X0,X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK1,sK0,sK3,sK2) != X0
    | u1_struct_0(sK2) != X3
    | u1_struct_0(sK0) != X4
    | u1_struct_0(sK0) != X2
    | u1_struct_0(sK1) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_487,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_519,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_431,c_487])).

cnf(c_790,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | sP0_iProver_split
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_519])).

cnf(c_1466,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_4575,plain,
    ( sK3 != sK3
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_4570,c_1466])).

cnf(c_4576,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4575])).

cnf(c_44,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_789,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_519])).

cnf(c_1467,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK0)
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_2056,plain,
    ( v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1467])).

cnf(c_6257,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4576,c_34,c_36,c_42,c_43,c_44,c_2056])).

cnf(c_6258,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6257])).

cnf(c_6263,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1489,c_6258])).

cnf(c_6609,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6606,c_6263])).

cnf(c_1862,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2102,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1862])).

cnf(c_2103,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2102])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6609,c_2103,c_44,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:40:31 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.96/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/0.99  
% 2.96/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.96/0.99  
% 2.96/0.99  ------  iProver source info
% 2.96/0.99  
% 2.96/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.96/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.96/0.99  git: non_committed_changes: false
% 2.96/0.99  git: last_make_outside_of_git: false
% 2.96/0.99  
% 2.96/0.99  ------ 
% 2.96/0.99  
% 2.96/0.99  ------ Input Options
% 2.96/0.99  
% 2.96/0.99  --out_options                           all
% 2.96/0.99  --tptp_safe_out                         true
% 2.96/0.99  --problem_path                          ""
% 2.96/0.99  --include_path                          ""
% 2.96/0.99  --clausifier                            res/vclausify_rel
% 2.96/0.99  --clausifier_options                    --mode clausify
% 2.96/0.99  --stdin                                 false
% 2.96/0.99  --stats_out                             all
% 2.96/0.99  
% 2.96/0.99  ------ General Options
% 2.96/0.99  
% 2.96/0.99  --fof                                   false
% 2.96/0.99  --time_out_real                         305.
% 2.96/0.99  --time_out_virtual                      -1.
% 2.96/0.99  --symbol_type_check                     false
% 2.96/0.99  --clausify_out                          false
% 2.96/0.99  --sig_cnt_out                           false
% 2.96/0.99  --trig_cnt_out                          false
% 2.96/0.99  --trig_cnt_out_tolerance                1.
% 2.96/0.99  --trig_cnt_out_sk_spl                   false
% 2.96/0.99  --abstr_cl_out                          false
% 2.96/0.99  
% 2.96/0.99  ------ Global Options
% 2.96/0.99  
% 2.96/0.99  --schedule                              default
% 2.96/0.99  --add_important_lit                     false
% 2.96/0.99  --prop_solver_per_cl                    1000
% 2.96/0.99  --min_unsat_core                        false
% 2.96/0.99  --soft_assumptions                      false
% 2.96/0.99  --soft_lemma_size                       3
% 2.96/0.99  --prop_impl_unit_size                   0
% 2.96/0.99  --prop_impl_unit                        []
% 2.96/0.99  --share_sel_clauses                     true
% 2.96/0.99  --reset_solvers                         false
% 2.96/0.99  --bc_imp_inh                            [conj_cone]
% 2.96/0.99  --conj_cone_tolerance                   3.
% 2.96/0.99  --extra_neg_conj                        none
% 2.96/0.99  --large_theory_mode                     true
% 2.96/0.99  --prolific_symb_bound                   200
% 2.96/0.99  --lt_threshold                          2000
% 2.96/0.99  --clause_weak_htbl                      true
% 2.96/0.99  --gc_record_bc_elim                     false
% 2.96/0.99  
% 2.96/0.99  ------ Preprocessing Options
% 2.96/0.99  
% 2.96/0.99  --preprocessing_flag                    true
% 2.96/0.99  --time_out_prep_mult                    0.1
% 2.96/0.99  --splitting_mode                        input
% 2.96/0.99  --splitting_grd                         true
% 2.96/0.99  --splitting_cvd                         false
% 2.96/0.99  --splitting_cvd_svl                     false
% 2.96/0.99  --splitting_nvd                         32
% 2.96/0.99  --sub_typing                            true
% 2.96/0.99  --prep_gs_sim                           true
% 2.96/0.99  --prep_unflatten                        true
% 2.96/0.99  --prep_res_sim                          true
% 2.96/0.99  --prep_upred                            true
% 2.96/0.99  --prep_sem_filter                       exhaustive
% 2.96/0.99  --prep_sem_filter_out                   false
% 2.96/0.99  --pred_elim                             true
% 2.96/0.99  --res_sim_input                         true
% 2.96/0.99  --eq_ax_congr_red                       true
% 2.96/0.99  --pure_diseq_elim                       true
% 2.96/0.99  --brand_transform                       false
% 2.96/0.99  --non_eq_to_eq                          false
% 2.96/0.99  --prep_def_merge                        true
% 2.96/0.99  --prep_def_merge_prop_impl              false
% 2.96/0.99  --prep_def_merge_mbd                    true
% 2.96/0.99  --prep_def_merge_tr_red                 false
% 2.96/0.99  --prep_def_merge_tr_cl                  false
% 2.96/0.99  --smt_preprocessing                     true
% 2.96/0.99  --smt_ac_axioms                         fast
% 2.96/0.99  --preprocessed_out                      false
% 2.96/0.99  --preprocessed_stats                    false
% 2.96/0.99  
% 2.96/0.99  ------ Abstraction refinement Options
% 2.96/0.99  
% 2.96/0.99  --abstr_ref                             []
% 2.96/0.99  --abstr_ref_prep                        false
% 2.96/0.99  --abstr_ref_until_sat                   false
% 2.96/0.99  --abstr_ref_sig_restrict                funpre
% 2.96/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.96/0.99  --abstr_ref_under                       []
% 2.96/0.99  
% 2.96/0.99  ------ SAT Options
% 2.96/0.99  
% 2.96/0.99  --sat_mode                              false
% 2.96/0.99  --sat_fm_restart_options                ""
% 2.96/0.99  --sat_gr_def                            false
% 2.96/0.99  --sat_epr_types                         true
% 2.96/0.99  --sat_non_cyclic_types                  false
% 2.96/0.99  --sat_finite_models                     false
% 2.96/0.99  --sat_fm_lemmas                         false
% 2.96/0.99  --sat_fm_prep                           false
% 2.96/0.99  --sat_fm_uc_incr                        true
% 2.96/0.99  --sat_out_model                         small
% 2.96/0.99  --sat_out_clauses                       false
% 2.96/0.99  
% 2.96/0.99  ------ QBF Options
% 2.96/0.99  
% 2.96/0.99  --qbf_mode                              false
% 2.96/0.99  --qbf_elim_univ                         false
% 2.96/0.99  --qbf_dom_inst                          none
% 2.96/0.99  --qbf_dom_pre_inst                      false
% 2.96/0.99  --qbf_sk_in                             false
% 2.96/0.99  --qbf_pred_elim                         true
% 2.96/0.99  --qbf_split                             512
% 2.96/0.99  
% 2.96/0.99  ------ BMC1 Options
% 2.96/0.99  
% 2.96/0.99  --bmc1_incremental                      false
% 2.96/0.99  --bmc1_axioms                           reachable_all
% 2.96/0.99  --bmc1_min_bound                        0
% 2.96/0.99  --bmc1_max_bound                        -1
% 2.96/0.99  --bmc1_max_bound_default                -1
% 2.96/0.99  --bmc1_symbol_reachability              true
% 2.96/0.99  --bmc1_property_lemmas                  false
% 2.96/0.99  --bmc1_k_induction                      false
% 2.96/0.99  --bmc1_non_equiv_states                 false
% 2.96/0.99  --bmc1_deadlock                         false
% 2.96/0.99  --bmc1_ucm                              false
% 2.96/0.99  --bmc1_add_unsat_core                   none
% 2.96/0.99  --bmc1_unsat_core_children              false
% 2.96/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.96/0.99  --bmc1_out_stat                         full
% 2.96/0.99  --bmc1_ground_init                      false
% 2.96/0.99  --bmc1_pre_inst_next_state              false
% 2.96/0.99  --bmc1_pre_inst_state                   false
% 2.96/0.99  --bmc1_pre_inst_reach_state             false
% 2.96/0.99  --bmc1_out_unsat_core                   false
% 2.96/0.99  --bmc1_aig_witness_out                  false
% 2.96/0.99  --bmc1_verbose                          false
% 2.96/0.99  --bmc1_dump_clauses_tptp                false
% 2.96/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.96/0.99  --bmc1_dump_file                        -
% 2.96/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.96/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.96/0.99  --bmc1_ucm_extend_mode                  1
% 2.96/0.99  --bmc1_ucm_init_mode                    2
% 2.96/0.99  --bmc1_ucm_cone_mode                    none
% 2.96/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.96/0.99  --bmc1_ucm_relax_model                  4
% 2.96/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.96/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.96/0.99  --bmc1_ucm_layered_model                none
% 2.96/0.99  --bmc1_ucm_max_lemma_size               10
% 2.96/0.99  
% 2.96/0.99  ------ AIG Options
% 2.96/0.99  
% 2.96/0.99  --aig_mode                              false
% 2.96/0.99  
% 2.96/0.99  ------ Instantiation Options
% 2.96/0.99  
% 2.96/0.99  --instantiation_flag                    true
% 2.96/0.99  --inst_sos_flag                         false
% 2.96/0.99  --inst_sos_phase                        true
% 2.96/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.96/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.96/0.99  --inst_lit_sel_side                     num_symb
% 2.96/0.99  --inst_solver_per_active                1400
% 2.96/0.99  --inst_solver_calls_frac                1.
% 2.96/0.99  --inst_passive_queue_type               priority_queues
% 2.96/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.96/0.99  --inst_passive_queues_freq              [25;2]
% 2.96/0.99  --inst_dismatching                      true
% 2.96/0.99  --inst_eager_unprocessed_to_passive     true
% 2.96/0.99  --inst_prop_sim_given                   true
% 2.96/0.99  --inst_prop_sim_new                     false
% 2.96/0.99  --inst_subs_new                         false
% 2.96/0.99  --inst_eq_res_simp                      false
% 2.96/0.99  --inst_subs_given                       false
% 2.96/0.99  --inst_orphan_elimination               true
% 2.96/0.99  --inst_learning_loop_flag               true
% 2.96/0.99  --inst_learning_start                   3000
% 2.96/0.99  --inst_learning_factor                  2
% 2.96/0.99  --inst_start_prop_sim_after_learn       3
% 2.96/0.99  --inst_sel_renew                        solver
% 2.96/0.99  --inst_lit_activity_flag                true
% 2.96/0.99  --inst_restr_to_given                   false
% 2.96/0.99  --inst_activity_threshold               500
% 2.96/0.99  --inst_out_proof                        true
% 2.96/0.99  
% 2.96/0.99  ------ Resolution Options
% 2.96/0.99  
% 2.96/0.99  --resolution_flag                       true
% 2.96/0.99  --res_lit_sel                           adaptive
% 2.96/0.99  --res_lit_sel_side                      none
% 2.96/0.99  --res_ordering                          kbo
% 2.96/0.99  --res_to_prop_solver                    active
% 2.96/0.99  --res_prop_simpl_new                    false
% 2.96/0.99  --res_prop_simpl_given                  true
% 2.96/0.99  --res_passive_queue_type                priority_queues
% 2.96/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.96/0.99  --res_passive_queues_freq               [15;5]
% 2.96/0.99  --res_forward_subs                      full
% 2.96/0.99  --res_backward_subs                     full
% 2.96/0.99  --res_forward_subs_resolution           true
% 2.96/0.99  --res_backward_subs_resolution          true
% 2.96/0.99  --res_orphan_elimination                true
% 2.96/0.99  --res_time_limit                        2.
% 2.96/0.99  --res_out_proof                         true
% 2.96/0.99  
% 2.96/0.99  ------ Superposition Options
% 2.96/0.99  
% 2.96/0.99  --superposition_flag                    true
% 2.96/0.99  --sup_passive_queue_type                priority_queues
% 2.96/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.96/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.96/0.99  --demod_completeness_check              fast
% 2.96/0.99  --demod_use_ground                      true
% 2.96/0.99  --sup_to_prop_solver                    passive
% 2.96/0.99  --sup_prop_simpl_new                    true
% 2.96/0.99  --sup_prop_simpl_given                  true
% 2.96/0.99  --sup_fun_splitting                     false
% 2.96/0.99  --sup_smt_interval                      50000
% 2.96/0.99  
% 2.96/0.99  ------ Superposition Simplification Setup
% 2.96/0.99  
% 2.96/0.99  --sup_indices_passive                   []
% 2.96/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.96/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.99  --sup_full_bw                           [BwDemod]
% 2.96/0.99  --sup_immed_triv                        [TrivRules]
% 2.96/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.96/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.99  --sup_immed_bw_main                     []
% 2.96/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.96/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/0.99  
% 2.96/0.99  ------ Combination Options
% 2.96/0.99  
% 2.96/0.99  --comb_res_mult                         3
% 2.96/0.99  --comb_sup_mult                         2
% 2.96/0.99  --comb_inst_mult                        10
% 2.96/0.99  
% 2.96/0.99  ------ Debug Options
% 2.96/0.99  
% 2.96/0.99  --dbg_backtrace                         false
% 2.96/0.99  --dbg_dump_prop_clauses                 false
% 2.96/0.99  --dbg_dump_prop_clauses_file            -
% 2.96/0.99  --dbg_out_stat                          false
% 2.96/0.99  ------ Parsing...
% 2.96/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.96/0.99  
% 2.96/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.96/0.99  
% 2.96/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.96/0.99  
% 2.96/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.96/0.99  ------ Proving...
% 2.96/0.99  ------ Problem Properties 
% 2.96/0.99  
% 2.96/0.99  
% 2.96/0.99  clauses                                 27
% 2.96/0.99  conjectures                             12
% 2.96/0.99  EPR                                     13
% 2.96/0.99  Horn                                    26
% 2.96/0.99  unary                                   13
% 2.96/0.99  binary                                  3
% 2.96/0.99  lits                                    67
% 2.96/0.99  lits eq                                 6
% 2.96/0.99  fd_pure                                 0
% 2.96/0.99  fd_pseudo                               0
% 2.96/0.99  fd_cond                                 0
% 2.96/0.99  fd_pseudo_cond                          1
% 2.96/0.99  AC symbols                              0
% 2.96/0.99  
% 2.96/0.99  ------ Schedule dynamic 5 is on 
% 2.96/0.99  
% 2.96/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.96/0.99  
% 2.96/0.99  
% 2.96/0.99  ------ 
% 2.96/0.99  Current options:
% 2.96/0.99  ------ 
% 2.96/0.99  
% 2.96/0.99  ------ Input Options
% 2.96/0.99  
% 2.96/0.99  --out_options                           all
% 2.96/0.99  --tptp_safe_out                         true
% 2.96/0.99  --problem_path                          ""
% 2.96/0.99  --include_path                          ""
% 2.96/0.99  --clausifier                            res/vclausify_rel
% 2.96/0.99  --clausifier_options                    --mode clausify
% 2.96/0.99  --stdin                                 false
% 2.96/0.99  --stats_out                             all
% 2.96/0.99  
% 2.96/0.99  ------ General Options
% 2.96/0.99  
% 2.96/0.99  --fof                                   false
% 2.96/0.99  --time_out_real                         305.
% 2.96/0.99  --time_out_virtual                      -1.
% 2.96/0.99  --symbol_type_check                     false
% 2.96/0.99  --clausify_out                          false
% 2.96/0.99  --sig_cnt_out                           false
% 2.96/0.99  --trig_cnt_out                          false
% 2.96/0.99  --trig_cnt_out_tolerance                1.
% 2.96/0.99  --trig_cnt_out_sk_spl                   false
% 2.96/0.99  --abstr_cl_out                          false
% 2.96/0.99  
% 2.96/0.99  ------ Global Options
% 2.96/0.99  
% 2.96/0.99  --schedule                              default
% 2.96/0.99  --add_important_lit                     false
% 2.96/0.99  --prop_solver_per_cl                    1000
% 2.96/0.99  --min_unsat_core                        false
% 2.96/0.99  --soft_assumptions                      false
% 2.96/0.99  --soft_lemma_size                       3
% 2.96/0.99  --prop_impl_unit_size                   0
% 2.96/0.99  --prop_impl_unit                        []
% 2.96/0.99  --share_sel_clauses                     true
% 2.96/0.99  --reset_solvers                         false
% 2.96/0.99  --bc_imp_inh                            [conj_cone]
% 2.96/0.99  --conj_cone_tolerance                   3.
% 2.96/0.99  --extra_neg_conj                        none
% 2.96/0.99  --large_theory_mode                     true
% 2.96/0.99  --prolific_symb_bound                   200
% 2.96/0.99  --lt_threshold                          2000
% 2.96/0.99  --clause_weak_htbl                      true
% 2.96/0.99  --gc_record_bc_elim                     false
% 2.96/0.99  
% 2.96/0.99  ------ Preprocessing Options
% 2.96/0.99  
% 2.96/0.99  --preprocessing_flag                    true
% 2.96/0.99  --time_out_prep_mult                    0.1
% 2.96/0.99  --splitting_mode                        input
% 2.96/0.99  --splitting_grd                         true
% 2.96/0.99  --splitting_cvd                         false
% 2.96/0.99  --splitting_cvd_svl                     false
% 2.96/0.99  --splitting_nvd                         32
% 2.96/0.99  --sub_typing                            true
% 2.96/0.99  --prep_gs_sim                           true
% 2.96/0.99  --prep_unflatten                        true
% 2.96/0.99  --prep_res_sim                          true
% 2.96/0.99  --prep_upred                            true
% 2.96/0.99  --prep_sem_filter                       exhaustive
% 2.96/0.99  --prep_sem_filter_out                   false
% 2.96/0.99  --pred_elim                             true
% 2.96/0.99  --res_sim_input                         true
% 2.96/0.99  --eq_ax_congr_red                       true
% 2.96/0.99  --pure_diseq_elim                       true
% 2.96/0.99  --brand_transform                       false
% 2.96/0.99  --non_eq_to_eq                          false
% 2.96/0.99  --prep_def_merge                        true
% 2.96/0.99  --prep_def_merge_prop_impl              false
% 2.96/0.99  --prep_def_merge_mbd                    true
% 2.96/0.99  --prep_def_merge_tr_red                 false
% 2.96/0.99  --prep_def_merge_tr_cl                  false
% 2.96/0.99  --smt_preprocessing                     true
% 2.96/0.99  --smt_ac_axioms                         fast
% 2.96/0.99  --preprocessed_out                      false
% 2.96/0.99  --preprocessed_stats                    false
% 2.96/0.99  
% 2.96/0.99  ------ Abstraction refinement Options
% 2.96/0.99  
% 2.96/0.99  --abstr_ref                             []
% 2.96/0.99  --abstr_ref_prep                        false
% 2.96/0.99  --abstr_ref_until_sat                   false
% 2.96/0.99  --abstr_ref_sig_restrict                funpre
% 2.96/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.96/0.99  --abstr_ref_under                       []
% 2.96/0.99  
% 2.96/0.99  ------ SAT Options
% 2.96/0.99  
% 2.96/0.99  --sat_mode                              false
% 2.96/0.99  --sat_fm_restart_options                ""
% 2.96/0.99  --sat_gr_def                            false
% 2.96/0.99  --sat_epr_types                         true
% 2.96/0.99  --sat_non_cyclic_types                  false
% 2.96/0.99  --sat_finite_models                     false
% 2.96/0.99  --sat_fm_lemmas                         false
% 2.96/0.99  --sat_fm_prep                           false
% 2.96/0.99  --sat_fm_uc_incr                        true
% 2.96/0.99  --sat_out_model                         small
% 2.96/0.99  --sat_out_clauses                       false
% 2.96/0.99  
% 2.96/0.99  ------ QBF Options
% 2.96/0.99  
% 2.96/0.99  --qbf_mode                              false
% 2.96/0.99  --qbf_elim_univ                         false
% 2.96/0.99  --qbf_dom_inst                          none
% 2.96/0.99  --qbf_dom_pre_inst                      false
% 2.96/0.99  --qbf_sk_in                             false
% 2.96/0.99  --qbf_pred_elim                         true
% 2.96/0.99  --qbf_split                             512
% 2.96/0.99  
% 2.96/0.99  ------ BMC1 Options
% 2.96/0.99  
% 2.96/0.99  --bmc1_incremental                      false
% 2.96/0.99  --bmc1_axioms                           reachable_all
% 2.96/0.99  --bmc1_min_bound                        0
% 2.96/0.99  --bmc1_max_bound                        -1
% 2.96/0.99  --bmc1_max_bound_default                -1
% 2.96/0.99  --bmc1_symbol_reachability              true
% 2.96/0.99  --bmc1_property_lemmas                  false
% 2.96/0.99  --bmc1_k_induction                      false
% 2.96/0.99  --bmc1_non_equiv_states                 false
% 2.96/0.99  --bmc1_deadlock                         false
% 2.96/0.99  --bmc1_ucm                              false
% 2.96/0.99  --bmc1_add_unsat_core                   none
% 2.96/0.99  --bmc1_unsat_core_children              false
% 2.96/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.96/0.99  --bmc1_out_stat                         full
% 2.96/0.99  --bmc1_ground_init                      false
% 2.96/0.99  --bmc1_pre_inst_next_state              false
% 2.96/0.99  --bmc1_pre_inst_state                   false
% 2.96/0.99  --bmc1_pre_inst_reach_state             false
% 2.96/0.99  --bmc1_out_unsat_core                   false
% 2.96/0.99  --bmc1_aig_witness_out                  false
% 2.96/0.99  --bmc1_verbose                          false
% 2.96/0.99  --bmc1_dump_clauses_tptp                false
% 2.96/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.96/0.99  --bmc1_dump_file                        -
% 2.96/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.96/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.96/0.99  --bmc1_ucm_extend_mode                  1
% 2.96/0.99  --bmc1_ucm_init_mode                    2
% 2.96/0.99  --bmc1_ucm_cone_mode                    none
% 2.96/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.96/0.99  --bmc1_ucm_relax_model                  4
% 2.96/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.96/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.96/0.99  --bmc1_ucm_layered_model                none
% 2.96/0.99  --bmc1_ucm_max_lemma_size               10
% 2.96/0.99  
% 2.96/0.99  ------ AIG Options
% 2.96/0.99  
% 2.96/0.99  --aig_mode                              false
% 2.96/0.99  
% 2.96/0.99  ------ Instantiation Options
% 2.96/0.99  
% 2.96/0.99  --instantiation_flag                    true
% 2.96/0.99  --inst_sos_flag                         false
% 2.96/0.99  --inst_sos_phase                        true
% 2.96/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.96/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.96/0.99  --inst_lit_sel_side                     none
% 2.96/0.99  --inst_solver_per_active                1400
% 2.96/0.99  --inst_solver_calls_frac                1.
% 2.96/0.99  --inst_passive_queue_type               priority_queues
% 2.96/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.96/0.99  --inst_passive_queues_freq              [25;2]
% 2.96/0.99  --inst_dismatching                      true
% 2.96/0.99  --inst_eager_unprocessed_to_passive     true
% 2.96/0.99  --inst_prop_sim_given                   true
% 2.96/0.99  --inst_prop_sim_new                     false
% 2.96/0.99  --inst_subs_new                         false
% 2.96/0.99  --inst_eq_res_simp                      false
% 2.96/0.99  --inst_subs_given                       false
% 2.96/0.99  --inst_orphan_elimination               true
% 2.96/0.99  --inst_learning_loop_flag               true
% 2.96/0.99  --inst_learning_start                   3000
% 2.96/0.99  --inst_learning_factor                  2
% 2.96/0.99  --inst_start_prop_sim_after_learn       3
% 2.96/0.99  --inst_sel_renew                        solver
% 2.96/0.99  --inst_lit_activity_flag                true
% 2.96/0.99  --inst_restr_to_given                   false
% 2.96/0.99  --inst_activity_threshold               500
% 2.96/0.99  --inst_out_proof                        true
% 2.96/0.99  
% 2.96/0.99  ------ Resolution Options
% 2.96/0.99  
% 2.96/0.99  --resolution_flag                       false
% 2.96/0.99  --res_lit_sel                           adaptive
% 2.96/0.99  --res_lit_sel_side                      none
% 2.96/0.99  --res_ordering                          kbo
% 2.96/0.99  --res_to_prop_solver                    active
% 2.96/0.99  --res_prop_simpl_new                    false
% 2.96/0.99  --res_prop_simpl_given                  true
% 2.96/0.99  --res_passive_queue_type                priority_queues
% 2.96/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.96/0.99  --res_passive_queues_freq               [15;5]
% 2.96/0.99  --res_forward_subs                      full
% 2.96/0.99  --res_backward_subs                     full
% 2.96/0.99  --res_forward_subs_resolution           true
% 2.96/0.99  --res_backward_subs_resolution          true
% 2.96/0.99  --res_orphan_elimination                true
% 2.96/0.99  --res_time_limit                        2.
% 2.96/0.99  --res_out_proof                         true
% 2.96/0.99  
% 2.96/0.99  ------ Superposition Options
% 2.96/0.99  
% 2.96/0.99  --superposition_flag                    true
% 2.96/0.99  --sup_passive_queue_type                priority_queues
% 2.96/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.96/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.96/0.99  --demod_completeness_check              fast
% 2.96/0.99  --demod_use_ground                      true
% 2.96/0.99  --sup_to_prop_solver                    passive
% 2.96/0.99  --sup_prop_simpl_new                    true
% 2.96/0.99  --sup_prop_simpl_given                  true
% 2.96/0.99  --sup_fun_splitting                     false
% 2.96/0.99  --sup_smt_interval                      50000
% 2.96/0.99  
% 2.96/0.99  ------ Superposition Simplification Setup
% 2.96/0.99  
% 2.96/0.99  --sup_indices_passive                   []
% 2.96/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.96/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.99  --sup_full_bw                           [BwDemod]
% 2.96/0.99  --sup_immed_triv                        [TrivRules]
% 2.96/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.96/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.99  --sup_immed_bw_main                     []
% 2.96/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.96/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/0.99  
% 2.96/0.99  ------ Combination Options
% 2.96/0.99  
% 2.96/0.99  --comb_res_mult                         3
% 2.96/0.99  --comb_sup_mult                         2
% 2.96/0.99  --comb_inst_mult                        10
% 2.96/0.99  
% 2.96/0.99  ------ Debug Options
% 2.96/0.99  
% 2.96/0.99  --dbg_backtrace                         false
% 2.96/0.99  --dbg_dump_prop_clauses                 false
% 2.96/0.99  --dbg_dump_prop_clauses_file            -
% 2.96/0.99  --dbg_out_stat                          false
% 2.96/0.99  
% 2.96/0.99  
% 2.96/0.99  
% 2.96/0.99  
% 2.96/0.99  ------ Proving...
% 2.96/0.99  
% 2.96/0.99  
% 2.96/0.99  % SZS status Theorem for theBenchmark.p
% 2.96/0.99  
% 2.96/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.96/0.99  
% 2.96/0.99  fof(f15,conjecture,(
% 2.96/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 2.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.99  
% 2.96/0.99  fof(f16,negated_conjecture,(
% 2.96/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 2.96/0.99    inference(negated_conjecture,[],[f15])).
% 2.96/0.99  
% 2.96/0.99  fof(f35,plain,(
% 2.96/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.96/0.99    inference(ennf_transformation,[],[f16])).
% 2.96/0.99  
% 2.96/0.99  fof(f36,plain,(
% 2.96/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.96/0.99    inference(flattening,[],[f35])).
% 2.96/0.99  
% 2.96/0.99  fof(f46,plain,(
% 2.96/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 2.96/0.99    introduced(choice_axiom,[])).
% 2.96/0.99  
% 2.96/0.99  fof(f45,plain,(
% 2.96/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 2.96/0.99    introduced(choice_axiom,[])).
% 2.96/0.99  
% 2.96/0.99  fof(f44,plain,(
% 2.96/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.96/0.99    introduced(choice_axiom,[])).
% 2.96/0.99  
% 2.96/0.99  fof(f43,plain,(
% 2.96/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.96/0.99    introduced(choice_axiom,[])).
% 2.96/0.99  
% 2.96/0.99  fof(f47,plain,(
% 2.96/0.99    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.96/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f46,f45,f44,f43])).
% 2.96/0.99  
% 2.96/0.99  fof(f76,plain,(
% 2.96/0.99    m1_pre_topc(sK2,sK1)),
% 2.96/0.99    inference(cnf_transformation,[],[f47])).
% 2.96/0.99  
% 2.96/0.99  fof(f13,axiom,(
% 2.96/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.99  
% 2.96/0.99  fof(f33,plain,(
% 2.96/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.96/0.99    inference(ennf_transformation,[],[f13])).
% 2.96/0.99  
% 2.96/0.99  fof(f67,plain,(
% 2.96/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.96/0.99    inference(cnf_transformation,[],[f33])).
% 2.96/0.99  
% 2.96/0.99  fof(f2,axiom,(
% 2.96/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.99  
% 2.96/0.99  fof(f39,plain,(
% 2.96/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.96/0.99    inference(nnf_transformation,[],[f2])).
% 2.96/0.99  
% 2.96/0.99  fof(f51,plain,(
% 2.96/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.96/0.99    inference(cnf_transformation,[],[f39])).
% 2.96/0.99  
% 2.96/0.99  fof(f1,axiom,(
% 2.96/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.99  
% 2.96/0.99  fof(f37,plain,(
% 2.96/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.96/0.99    inference(nnf_transformation,[],[f1])).
% 2.96/0.99  
% 2.96/0.99  fof(f38,plain,(
% 2.96/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.96/0.99    inference(flattening,[],[f37])).
% 2.96/0.99  
% 2.96/0.99  fof(f50,plain,(
% 2.96/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.96/0.99    inference(cnf_transformation,[],[f38])).
% 2.96/0.99  
% 2.96/0.99  fof(f7,axiom,(
% 2.96/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.99  
% 2.96/0.99  fof(f24,plain,(
% 2.96/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.96/0.99    inference(ennf_transformation,[],[f7])).
% 2.96/0.99  
% 2.96/0.99  fof(f59,plain,(
% 2.96/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.96/0.99    inference(cnf_transformation,[],[f24])).
% 2.96/0.99  
% 2.96/0.99  fof(f74,plain,(
% 2.96/0.99    l1_pre_topc(sK1)),
% 2.96/0.99    inference(cnf_transformation,[],[f47])).
% 2.96/0.99  
% 2.96/0.99  fof(f14,axiom,(
% 2.96/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.99  
% 2.96/0.99  fof(f34,plain,(
% 2.96/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.96/0.99    inference(ennf_transformation,[],[f14])).
% 2.96/0.99  
% 2.96/0.99  fof(f68,plain,(
% 2.96/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.96/0.99    inference(cnf_transformation,[],[f34])).
% 2.96/0.99  
% 2.96/0.99  fof(f10,axiom,(
% 2.96/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.99  
% 2.96/0.99  fof(f28,plain,(
% 2.96/0.99    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.96/0.99    inference(ennf_transformation,[],[f10])).
% 2.96/0.99  
% 2.96/0.99  fof(f41,plain,(
% 2.96/0.99    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.96/0.99    inference(nnf_transformation,[],[f28])).
% 2.96/0.99  
% 2.96/0.99  fof(f62,plain,(
% 2.96/0.99    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.96/0.99    inference(cnf_transformation,[],[f41])).
% 2.96/0.99  
% 2.96/0.99  fof(f80,plain,(
% 2.96/0.99    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 2.96/0.99    inference(cnf_transformation,[],[f47])).
% 2.96/0.99  
% 2.96/0.99  fof(f9,axiom,(
% 2.96/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 2.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.99  
% 2.96/0.99  fof(f27,plain,(
% 2.96/0.99    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.96/0.99    inference(ennf_transformation,[],[f9])).
% 2.96/0.99  
% 2.96/0.99  fof(f61,plain,(
% 2.96/0.99    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 2.96/0.99    inference(cnf_transformation,[],[f27])).
% 2.96/0.99  
% 2.96/0.99  fof(f52,plain,(
% 2.96/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.96/0.99    inference(cnf_transformation,[],[f39])).
% 2.96/0.99  
% 2.96/0.99  fof(f79,plain,(
% 2.96/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.96/0.99    inference(cnf_transformation,[],[f47])).
% 2.96/0.99  
% 2.96/0.99  fof(f3,axiom,(
% 2.96/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.99  
% 2.96/0.99  fof(f17,plain,(
% 2.96/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.96/0.99    inference(ennf_transformation,[],[f3])).
% 2.96/0.99  
% 2.96/0.99  fof(f18,plain,(
% 2.96/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.96/0.99    inference(flattening,[],[f17])).
% 2.96/0.99  
% 2.96/0.99  fof(f40,plain,(
% 2.96/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.96/0.99    inference(nnf_transformation,[],[f18])).
% 2.96/0.99  
% 2.96/0.99  fof(f53,plain,(
% 2.96/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.96/0.99    inference(cnf_transformation,[],[f40])).
% 2.96/0.99  
% 2.96/0.99  fof(f5,axiom,(
% 2.96/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 2.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.99  
% 2.96/0.99  fof(f21,plain,(
% 2.96/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.96/0.99    inference(ennf_transformation,[],[f5])).
% 2.96/0.99  
% 2.96/0.99  fof(f22,plain,(
% 2.96/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.96/0.99    inference(flattening,[],[f21])).
% 2.96/0.99  
% 2.96/0.99  fof(f57,plain,(
% 2.96/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.96/0.99    inference(cnf_transformation,[],[f22])).
% 2.96/0.99  
% 2.96/0.99  fof(f4,axiom,(
% 2.96/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 2.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.99  
% 2.96/0.99  fof(f19,plain,(
% 2.96/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.96/0.99    inference(ennf_transformation,[],[f4])).
% 2.96/0.99  
% 2.96/0.99  fof(f20,plain,(
% 2.96/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.96/0.99    inference(flattening,[],[f19])).
% 2.96/0.99  
% 2.96/0.99  fof(f56,plain,(
% 2.96/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.96/0.99    inference(cnf_transformation,[],[f20])).
% 2.96/0.99  
% 2.96/0.99  fof(f77,plain,(
% 2.96/0.99    v1_funct_1(sK3)),
% 2.96/0.99    inference(cnf_transformation,[],[f47])).
% 2.96/0.99  
% 2.96/0.99  fof(f78,plain,(
% 2.96/0.99    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.96/0.99    inference(cnf_transformation,[],[f47])).
% 2.96/0.99  
% 2.96/0.99  fof(f12,axiom,(
% 2.96/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 2.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.99  
% 2.96/0.99  fof(f31,plain,(
% 2.96/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.96/0.99    inference(ennf_transformation,[],[f12])).
% 2.96/0.99  
% 2.96/0.99  fof(f32,plain,(
% 2.96/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/0.99    inference(flattening,[],[f31])).
% 2.96/0.99  
% 2.96/0.99  fof(f66,plain,(
% 2.96/0.99    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/0.99    inference(cnf_transformation,[],[f32])).
% 2.96/0.99  
% 2.96/0.99  fof(f69,plain,(
% 2.96/0.99    ~v2_struct_0(sK0)),
% 2.96/0.99    inference(cnf_transformation,[],[f47])).
% 2.96/0.99  
% 2.96/0.99  fof(f70,plain,(
% 2.96/0.99    v2_pre_topc(sK0)),
% 2.96/0.99    inference(cnf_transformation,[],[f47])).
% 2.96/0.99  
% 2.96/0.99  fof(f71,plain,(
% 2.96/0.99    l1_pre_topc(sK0)),
% 2.96/0.99    inference(cnf_transformation,[],[f47])).
% 2.96/0.99  
% 2.96/0.99  fof(f72,plain,(
% 2.96/0.99    ~v2_struct_0(sK1)),
% 2.96/0.99    inference(cnf_transformation,[],[f47])).
% 2.96/0.99  
% 2.96/0.99  fof(f73,plain,(
% 2.96/0.99    v2_pre_topc(sK1)),
% 2.96/0.99    inference(cnf_transformation,[],[f47])).
% 2.96/0.99  
% 2.96/0.99  fof(f6,axiom,(
% 2.96/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.99  
% 2.96/0.99  fof(f23,plain,(
% 2.96/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.96/0.99    inference(ennf_transformation,[],[f6])).
% 2.96/0.99  
% 2.96/0.99  fof(f58,plain,(
% 2.96/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.96/0.99    inference(cnf_transformation,[],[f23])).
% 2.96/0.99  
% 2.96/0.99  fof(f8,axiom,(
% 2.96/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.99  
% 2.96/0.99  fof(f25,plain,(
% 2.96/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.96/0.99    inference(ennf_transformation,[],[f8])).
% 2.96/0.99  
% 2.96/0.99  fof(f26,plain,(
% 2.96/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.96/0.99    inference(flattening,[],[f25])).
% 2.96/0.99  
% 2.96/0.99  fof(f60,plain,(
% 2.96/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.96/0.99    inference(cnf_transformation,[],[f26])).
% 2.96/0.99  
% 2.96/0.99  fof(f11,axiom,(
% 2.96/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 2.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.99  
% 2.96/0.99  fof(f29,plain,(
% 2.96/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.96/0.99    inference(ennf_transformation,[],[f11])).
% 2.96/0.99  
% 2.96/0.99  fof(f30,plain,(
% 2.96/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.96/0.99    inference(flattening,[],[f29])).
% 2.96/0.99  
% 2.96/0.99  fof(f42,plain,(
% 2.96/0.99    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.96/0.99    inference(nnf_transformation,[],[f30])).
% 2.96/0.99  
% 2.96/0.99  fof(f65,plain,(
% 2.96/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.96/0.99    inference(cnf_transformation,[],[f42])).
% 2.96/0.99  
% 2.96/0.99  fof(f85,plain,(
% 2.96/0.99    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.96/0.99    inference(equality_resolution,[],[f65])).
% 2.96/0.99  
% 2.96/0.99  fof(f81,plain,(
% 2.96/0.99    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 2.96/0.99    inference(cnf_transformation,[],[f47])).
% 2.96/0.99  
% 2.96/0.99  cnf(c_26,negated_conjecture,
% 2.96/0.99      ( m1_pre_topc(sK2,sK1) ),
% 2.96/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1477,plain,
% 2.96/0.99      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_19,plain,
% 2.96/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.96/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/0.99      | ~ l1_pre_topc(X1) ),
% 2.96/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1482,plain,
% 2.96/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 2.96/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 2.96/0.99      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_4,plain,
% 2.96/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.96/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1488,plain,
% 2.96/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.96/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2512,plain,
% 2.96/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 2.96/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 2.96/0.99      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.99      inference(superposition,[status(thm)],[c_1482,c_1488]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_0,plain,
% 2.96/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.96/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1491,plain,
% 2.96/0.99      ( X0 = X1
% 2.96/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.96/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2893,plain,
% 2.96/0.99      ( u1_struct_0(X0) = u1_struct_0(X1)
% 2.96/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 2.96/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 2.96/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.96/0.99      inference(superposition,[status(thm)],[c_2512,c_1491]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_4144,plain,
% 2.96/0.99      ( u1_struct_0(X0) = u1_struct_0(X1)
% 2.96/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 2.96/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 2.96/0.99      | l1_pre_topc(X1) != iProver_top
% 2.96/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.96/0.99      inference(superposition,[status(thm)],[c_2512,c_2893]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_11,plain,
% 2.96/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.96/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_69,plain,
% 2.96/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 2.96/0.99      | l1_pre_topc(X1) != iProver_top
% 2.96/0.99      | l1_pre_topc(X0) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6409,plain,
% 2.96/0.99      ( l1_pre_topc(X1) != iProver_top
% 2.96/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 2.96/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 2.96/0.99      | u1_struct_0(X0) = u1_struct_0(X1) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_4144,c_69,c_2512,c_2893]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6410,plain,
% 2.96/0.99      ( u1_struct_0(X0) = u1_struct_0(X1)
% 2.96/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 2.96/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 2.96/0.99      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_6409]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6419,plain,
% 2.96/0.99      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 2.96/0.99      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.96/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.99      inference(superposition,[status(thm)],[c_1477,c_6410]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_28,negated_conjecture,
% 2.96/0.99      ( l1_pre_topc(sK1) ),
% 2.96/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_39,plain,
% 2.96/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_20,plain,
% 2.96/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.96/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_46,plain,
% 2.96/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 2.96/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_48,plain,
% 2.96/0.99      ( m1_pre_topc(sK1,sK1) = iProver_top
% 2.96/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.99      inference(instantiation,[status(thm)],[c_46]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_15,plain,
% 2.96/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.96/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.96/0.99      | ~ l1_pre_topc(X0)
% 2.96/0.99      | ~ l1_pre_topc(X1) ),
% 2.96/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_61,plain,
% 2.96/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 2.96/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 2.96/0.99      | l1_pre_topc(X0) != iProver_top
% 2.96/0.99      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_63,plain,
% 2.96/0.99      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.96/0.99      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.96/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.99      inference(instantiation,[status(thm)],[c_61]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1485,plain,
% 2.96/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 2.96/0.99      | l1_pre_topc(X1) != iProver_top
% 2.96/0.99      | l1_pre_topc(X0) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2357,plain,
% 2.96/0.99      ( l1_pre_topc(sK2) = iProver_top
% 2.96/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.99      inference(superposition,[status(thm)],[c_1477,c_1485]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_22,negated_conjecture,
% 2.96/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 2.96/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_13,plain,
% 2.96/0.99      ( m1_pre_topc(X0,X1)
% 2.96/0.99      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.96/0.99      | ~ l1_pre_topc(X1) ),
% 2.96/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1484,plain,
% 2.96/0.99      ( m1_pre_topc(X0,X1) = iProver_top
% 2.96/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 2.96/0.99      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2618,plain,
% 2.96/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.96/0.99      | m1_pre_topc(X0,sK2) = iProver_top
% 2.96/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 2.96/0.99      inference(superposition,[status(thm)],[c_22,c_1484]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2635,plain,
% 2.96/0.99      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.96/0.99      | m1_pre_topc(sK1,sK2) = iProver_top
% 2.96/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 2.96/0.99      inference(instantiation,[status(thm)],[c_2618]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6606,plain,
% 2.96/0.99      ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_6419,c_39,c_48,c_63,c_2357,c_2635]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_3,plain,
% 2.96/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.96/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1489,plain,
% 2.96/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.96/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1481,plain,
% 2.96/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 2.96/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_185,plain,
% 2.96/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.96/0.99      | ~ m1_pre_topc(X0,X1)
% 2.96/0.99      | ~ l1_pre_topc(X1) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_15,c_11]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_186,plain,
% 2.96/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.96/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.96/0.99      | ~ l1_pre_topc(X1) ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_185]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1469,plain,
% 2.96/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 2.96/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 2.96/0.99      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2638,plain,
% 2.96/0.99      ( m1_pre_topc(X0,sK2) = iProver_top
% 2.96/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_2618,c_39,c_2357]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2639,plain,
% 2.96/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.96/0.99      | m1_pre_topc(X0,sK2) = iProver_top ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_2638]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_3039,plain,
% 2.96/0.99      ( m1_pre_topc(X0,sK2) = iProver_top
% 2.96/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 2.96/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.99      inference(superposition,[status(thm)],[c_1469,c_2639]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_3480,plain,
% 2.96/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.96/0.99      | m1_pre_topc(X0,sK2) = iProver_top ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_3039,c_39]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_3481,plain,
% 2.96/0.99      ( m1_pre_topc(X0,sK2) = iProver_top
% 2.96/0.99      | m1_pre_topc(X0,sK1) != iProver_top ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_3480]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_3488,plain,
% 2.96/0.99      ( m1_pre_topc(sK1,sK2) = iProver_top
% 2.96/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.99      inference(superposition,[status(thm)],[c_1481,c_3481]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_3989,plain,
% 2.96/0.99      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_3488,c_39,c_48,c_63,c_2357,c_2635]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_23,negated_conjecture,
% 2.96/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 2.96/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1480,plain,
% 2.96/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6,plain,
% 2.96/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.96/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.96/0.99      | X2 = X3 ),
% 2.96/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_9,plain,
% 2.96/0.99      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3),X2)
% 2.96/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.96/0.99      | ~ r1_tarski(X0,X3)
% 2.96/0.99      | ~ v1_funct_1(X2) ),
% 2.96/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_451,plain,
% 2.96/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.96/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.96/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.99      | ~ r1_tarski(X1,X7)
% 2.96/0.99      | ~ v1_funct_1(X0)
% 2.96/0.99      | X0 != X6
% 2.96/0.99      | X2 != X5
% 2.96/0.99      | X1 != X4
% 2.96/0.99      | X6 = X3
% 2.96/0.99      | k2_partfun1(X1,X2,X0,X7) != X3 ),
% 2.96/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_9]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_452,plain,
% 2.96/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.99      | ~ m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.99      | ~ r1_tarski(X1,X3)
% 2.96/0.99      | ~ v1_funct_1(X0)
% 2.96/0.99      | X0 = k2_partfun1(X1,X2,X0,X3) ),
% 2.96/0.99      inference(unflattening,[status(thm)],[c_451]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_7,plain,
% 2.96/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.99      | ~ v1_funct_1(X0) ),
% 2.96/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_456,plain,
% 2.96/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.99      | ~ v1_funct_2(X0,X1,X2)
% 2.96/0.99      | ~ r1_tarski(X1,X3)
% 2.96/0.99      | ~ v1_funct_1(X0)
% 2.96/0.99      | X0 = k2_partfun1(X1,X2,X0,X3) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_452,c_7]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_457,plain,
% 2.96/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.99      | ~ r1_tarski(X1,X3)
% 2.96/0.99      | ~ v1_funct_1(X0)
% 2.96/0.99      | X0 = k2_partfun1(X1,X2,X0,X3) ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_456]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1468,plain,
% 2.96/0.99      ( X0 = k2_partfun1(X1,X2,X0,X3)
% 2.96/0.99      | v1_funct_2(X0,X1,X2) != iProver_top
% 2.96/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.96/0.99      | r1_tarski(X1,X3) != iProver_top
% 2.96/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2327,plain,
% 2.96/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = sK3
% 2.96/0.99      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.96/0.99      | r1_tarski(u1_struct_0(sK1),X0) != iProver_top
% 2.96/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.96/0.99      inference(superposition,[status(thm)],[c_1480,c_1468]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_25,negated_conjecture,
% 2.96/0.99      ( v1_funct_1(sK3) ),
% 2.96/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_42,plain,
% 2.96/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_24,negated_conjecture,
% 2.96/0.99      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 2.96/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_43,plain,
% 2.96/0.99      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2800,plain,
% 2.96/0.99      ( r1_tarski(u1_struct_0(sK1),X0) != iProver_top
% 2.96/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = sK3 ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_2327,c_42,c_43]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2801,plain,
% 2.96/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = sK3
% 2.96/0.99      | r1_tarski(u1_struct_0(sK1),X0) != iProver_top ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_2800]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2894,plain,
% 2.96/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = sK3
% 2.96/0.99      | m1_pre_topc(sK1,X0) != iProver_top
% 2.96/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.96/0.99      inference(superposition,[status(thm)],[c_2512,c_2801]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_4396,plain,
% 2.96/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK3
% 2.96/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 2.96/0.99      inference(superposition,[status(thm)],[c_3989,c_2894]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_18,plain,
% 2.96/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.96/0.99      | ~ m1_pre_topc(X3,X1)
% 2.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.96/0.99      | ~ v2_pre_topc(X2)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | v2_struct_0(X2)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ l1_pre_topc(X2)
% 2.96/0.99      | ~ v1_funct_1(X0)
% 2.96/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.96/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1483,plain,
% 2.96/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
% 2.96/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 2.96/0.99      | m1_pre_topc(X3,X0) != iProver_top
% 2.96/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.96/0.99      | v2_pre_topc(X1) != iProver_top
% 2.96/0.99      | v2_pre_topc(X0) != iProver_top
% 2.96/0.99      | v2_struct_0(X0) = iProver_top
% 2.96/0.99      | v2_struct_0(X1) = iProver_top
% 2.96/0.99      | l1_pre_topc(X0) != iProver_top
% 2.96/0.99      | l1_pre_topc(X1) != iProver_top
% 2.96/0.99      | v1_funct_1(X2) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_3333,plain,
% 2.96/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 2.96/0.99      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.96/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 2.96/0.99      | v2_pre_topc(sK0) != iProver_top
% 2.96/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.96/0.99      | v2_struct_0(sK0) = iProver_top
% 2.96/0.99      | v2_struct_0(sK1) = iProver_top
% 2.96/0.99      | l1_pre_topc(sK0) != iProver_top
% 2.96/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.96/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.96/0.99      inference(superposition,[status(thm)],[c_1480,c_1483]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_33,negated_conjecture,
% 2.96/0.99      ( ~ v2_struct_0(sK0) ),
% 2.96/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_34,plain,
% 2.96/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_32,negated_conjecture,
% 2.96/0.99      ( v2_pre_topc(sK0) ),
% 2.96/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_35,plain,
% 2.96/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_31,negated_conjecture,
% 2.96/0.99      ( l1_pre_topc(sK0) ),
% 2.96/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_36,plain,
% 2.96/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_30,negated_conjecture,
% 2.96/0.99      ( ~ v2_struct_0(sK1) ),
% 2.96/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_37,plain,
% 2.96/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_29,negated_conjecture,
% 2.96/0.99      ( v2_pre_topc(sK1) ),
% 2.96/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_38,plain,
% 2.96/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_3726,plain,
% 2.96/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.96/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_3333,c_34,c_35,c_36,c_37,c_38,c_39,c_42,c_43]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_3727,plain,
% 2.96/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 2.96/0.99      | m1_pre_topc(X0,sK1) != iProver_top ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_3726]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_3735,plain,
% 2.96/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 2.96/1.00      inference(superposition,[status(thm)],[c_1477,c_3727]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4399,plain,
% 2.96/1.00      ( k2_tmap_1(sK1,sK0,sK3,sK2) = sK3
% 2.96/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.96/1.00      inference(demodulation,[status(thm)],[c_4396,c_3735]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4570,plain,
% 2.96/1.00      ( k2_tmap_1(sK1,sK0,sK3,sK2) = sK3 ),
% 2.96/1.00      inference(global_propositional_subsumption,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_4399,c_39,c_2357]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_10,plain,
% 2.96/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.96/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_12,plain,
% 2.96/1.00      ( v2_struct_0(X0)
% 2.96/1.00      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.96/1.00      | ~ l1_struct_0(X0) ),
% 2.96/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_431,plain,
% 2.96/1.00      ( v2_struct_0(X0)
% 2.96/1.00      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.96/1.00      | ~ l1_pre_topc(X0) ),
% 2.96/1.00      inference(resolution,[status(thm)],[c_10,c_12]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_16,plain,
% 2.96/1.00      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 2.96/1.00      | ~ v1_funct_2(X4,X2,X3)
% 2.96/1.00      | ~ v1_funct_2(X4,X0,X1)
% 2.96/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.96/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.96/1.00      | v1_xboole_0(X1)
% 2.96/1.00      | v1_xboole_0(X3)
% 2.96/1.00      | ~ v1_funct_1(X4) ),
% 2.96/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_21,negated_conjecture,
% 2.96/1.00      ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
% 2.96/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_486,plain,
% 2.96/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.96/1.00      | ~ v1_funct_2(X0,X3,X4)
% 2.96/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.96/1.00      | v1_xboole_0(X2)
% 2.96/1.00      | v1_xboole_0(X4)
% 2.96/1.00      | ~ v1_funct_1(X0)
% 2.96/1.00      | k2_tmap_1(sK1,sK0,sK3,sK2) != X0
% 2.96/1.00      | u1_struct_0(sK2) != X3
% 2.96/1.00      | u1_struct_0(sK0) != X4
% 2.96/1.00      | u1_struct_0(sK0) != X2
% 2.96/1.00      | u1_struct_0(sK1) != X1
% 2.96/1.00      | sK3 != X0 ),
% 2.96/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_487,plain,
% 2.96/1.00      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.96/1.00      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.96/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.96/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.96/1.00      | v1_xboole_0(u1_struct_0(sK0))
% 2.96/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 2.96/1.00      | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 2.96/1.00      inference(unflattening,[status(thm)],[c_486]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_519,plain,
% 2.96/1.00      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.96/1.00      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.96/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.96/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.96/1.00      | v2_struct_0(X0)
% 2.96/1.00      | ~ l1_pre_topc(X0)
% 2.96/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 2.96/1.00      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 2.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 2.96/1.00      inference(resolution_lifted,[status(thm)],[c_431,c_487]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_790,plain,
% 2.96/1.00      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.96/1.00      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.96/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.96/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.96/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 2.96/1.00      | sP0_iProver_split
% 2.96/1.00      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
% 2.96/1.00      inference(splitting,
% 2.96/1.00                [splitting(split),new_symbols(definition,[])],
% 2.96/1.00                [c_519]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_1466,plain,
% 2.96/1.00      ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 2.96/1.00      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.96/1.00      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.96/1.00      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.96/1.00      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.96/1.00      | v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) != iProver_top
% 2.96/1.00      | sP0_iProver_split = iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4575,plain,
% 2.96/1.00      ( sK3 != sK3
% 2.96/1.00      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.96/1.00      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.96/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.96/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.96/1.00      | v1_funct_1(sK3) != iProver_top
% 2.96/1.00      | sP0_iProver_split = iProver_top ),
% 2.96/1.00      inference(demodulation,[status(thm)],[c_4570,c_1466]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4576,plain,
% 2.96/1.00      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.96/1.00      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.96/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.96/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.96/1.00      | v1_funct_1(sK3) != iProver_top
% 2.96/1.00      | sP0_iProver_split = iProver_top ),
% 2.96/1.00      inference(equality_resolution_simp,[status(thm)],[c_4575]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_44,plain,
% 2.96/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_789,plain,
% 2.96/1.00      ( v2_struct_0(X0)
% 2.96/1.00      | ~ l1_pre_topc(X0)
% 2.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK0)
% 2.96/1.00      | ~ sP0_iProver_split ),
% 2.96/1.00      inference(splitting,
% 2.96/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.96/1.00                [c_519]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_1467,plain,
% 2.96/1.00      ( u1_struct_0(X0) != u1_struct_0(sK0)
% 2.96/1.00      | v2_struct_0(X0) = iProver_top
% 2.96/1.00      | l1_pre_topc(X0) != iProver_top
% 2.96/1.00      | sP0_iProver_split != iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_2056,plain,
% 2.96/1.00      ( v2_struct_0(sK0) = iProver_top
% 2.96/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.96/1.00      | sP0_iProver_split != iProver_top ),
% 2.96/1.00      inference(equality_resolution,[status(thm)],[c_1467]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_6257,plain,
% 2.96/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.96/1.00      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top ),
% 2.96/1.00      inference(global_propositional_subsumption,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_4576,c_34,c_36,c_42,c_43,c_44,c_2056]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_6258,plain,
% 2.96/1.00      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.96/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top ),
% 2.96/1.00      inference(renaming,[status(thm)],[c_6257]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_6263,plain,
% 2.96/1.00      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.96/1.00      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) != iProver_top ),
% 2.96/1.00      inference(superposition,[status(thm)],[c_1489,c_6258]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_6609,plain,
% 2.96/1.00      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.96/1.00      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top ),
% 2.96/1.00      inference(demodulation,[status(thm)],[c_6606,c_6263]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_1862,plain,
% 2.96/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.96/1.00      | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) ),
% 2.96/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_2102,plain,
% 2.96/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.96/1.00      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 2.96/1.00      inference(instantiation,[status(thm)],[c_1862]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_2103,plain,
% 2.96/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.96/1.00      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_2102]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(contradiction,plain,
% 2.96/1.00      ( $false ),
% 2.96/1.00      inference(minisat,[status(thm)],[c_6609,c_2103,c_44,c_43]) ).
% 2.96/1.00  
% 2.96/1.00  
% 2.96/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.96/1.00  
% 2.96/1.00  ------                               Statistics
% 2.96/1.00  
% 2.96/1.00  ------ General
% 2.96/1.00  
% 2.96/1.00  abstr_ref_over_cycles:                  0
% 2.96/1.00  abstr_ref_under_cycles:                 0
% 2.96/1.00  gc_basic_clause_elim:                   0
% 2.96/1.00  forced_gc_time:                         0
% 2.96/1.00  parsing_time:                           0.01
% 2.96/1.00  unif_index_cands_time:                  0.
% 2.96/1.00  unif_index_add_time:                    0.
% 2.96/1.00  orderings_time:                         0.
% 2.96/1.00  out_proof_time:                         0.01
% 2.96/1.00  total_time:                             0.229
% 2.96/1.00  num_of_symbols:                         55
% 2.96/1.00  num_of_terms:                           5079
% 2.96/1.00  
% 2.96/1.00  ------ Preprocessing
% 2.96/1.00  
% 2.96/1.00  num_of_splits:                          1
% 2.96/1.00  num_of_split_atoms:                     1
% 2.96/1.00  num_of_reused_defs:                     0
% 2.96/1.00  num_eq_ax_congr_red:                    13
% 2.96/1.00  num_of_sem_filtered_clauses:            1
% 2.96/1.00  num_of_subtypes:                        0
% 2.96/1.00  monotx_restored_types:                  0
% 2.96/1.00  sat_num_of_epr_types:                   0
% 2.96/1.00  sat_num_of_non_cyclic_types:            0
% 2.96/1.00  sat_guarded_non_collapsed_types:        0
% 2.96/1.00  num_pure_diseq_elim:                    0
% 2.96/1.00  simp_replaced_by:                       0
% 2.96/1.00  res_preprocessed:                       145
% 2.96/1.00  prep_upred:                             0
% 2.96/1.00  prep_unflattend:                        19
% 2.96/1.00  smt_new_axioms:                         0
% 2.96/1.00  pred_elim_cands:                        8
% 2.96/1.00  pred_elim:                              4
% 2.96/1.00  pred_elim_cl:                           6
% 2.96/1.00  pred_elim_cycles:                       6
% 2.96/1.00  merged_defs:                            8
% 2.96/1.00  merged_defs_ncl:                        0
% 2.96/1.00  bin_hyper_res:                          8
% 2.96/1.00  prep_cycles:                            4
% 2.96/1.00  pred_elim_time:                         0.005
% 2.96/1.00  splitting_time:                         0.
% 2.96/1.00  sem_filter_time:                        0.
% 2.96/1.00  monotx_time:                            0.
% 2.96/1.00  subtype_inf_time:                       0.
% 2.96/1.00  
% 2.96/1.00  ------ Problem properties
% 2.96/1.00  
% 2.96/1.00  clauses:                                27
% 2.96/1.00  conjectures:                            12
% 2.96/1.00  epr:                                    13
% 2.96/1.00  horn:                                   26
% 2.96/1.00  ground:                                 13
% 2.96/1.00  unary:                                  13
% 2.96/1.00  binary:                                 3
% 2.96/1.00  lits:                                   67
% 2.96/1.00  lits_eq:                                6
% 2.96/1.00  fd_pure:                                0
% 2.96/1.00  fd_pseudo:                              0
% 2.96/1.00  fd_cond:                                0
% 2.96/1.00  fd_pseudo_cond:                         1
% 2.96/1.00  ac_symbols:                             0
% 2.96/1.00  
% 2.96/1.00  ------ Propositional Solver
% 2.96/1.00  
% 2.96/1.00  prop_solver_calls:                      30
% 2.96/1.00  prop_fast_solver_calls:                 1129
% 2.96/1.00  smt_solver_calls:                       0
% 2.96/1.00  smt_fast_solver_calls:                  0
% 2.96/1.00  prop_num_of_clauses:                    1916
% 2.96/1.00  prop_preprocess_simplified:             6387
% 2.96/1.00  prop_fo_subsumed:                       34
% 2.96/1.00  prop_solver_time:                       0.
% 2.96/1.00  smt_solver_time:                        0.
% 2.96/1.00  smt_fast_solver_time:                   0.
% 2.96/1.00  prop_fast_solver_time:                  0.
% 2.96/1.00  prop_unsat_core_time:                   0.
% 2.96/1.00  
% 2.96/1.00  ------ QBF
% 2.96/1.00  
% 2.96/1.00  qbf_q_res:                              0
% 2.96/1.00  qbf_num_tautologies:                    0
% 2.96/1.00  qbf_prep_cycles:                        0
% 2.96/1.00  
% 2.96/1.00  ------ BMC1
% 2.96/1.00  
% 2.96/1.00  bmc1_current_bound:                     -1
% 2.96/1.00  bmc1_last_solved_bound:                 -1
% 2.96/1.00  bmc1_unsat_core_size:                   -1
% 2.96/1.00  bmc1_unsat_core_parents_size:           -1
% 2.96/1.00  bmc1_merge_next_fun:                    0
% 2.96/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.96/1.00  
% 2.96/1.00  ------ Instantiation
% 2.96/1.00  
% 2.96/1.00  inst_num_of_clauses:                    680
% 2.96/1.00  inst_num_in_passive:                    218
% 2.96/1.00  inst_num_in_active:                     400
% 2.96/1.00  inst_num_in_unprocessed:                62
% 2.96/1.00  inst_num_of_loops:                      410
% 2.96/1.00  inst_num_of_learning_restarts:          0
% 2.96/1.00  inst_num_moves_active_passive:          5
% 2.96/1.00  inst_lit_activity:                      0
% 2.96/1.00  inst_lit_activity_moves:                0
% 2.96/1.00  inst_num_tautologies:                   0
% 2.96/1.00  inst_num_prop_implied:                  0
% 2.96/1.00  inst_num_existing_simplified:           0
% 2.96/1.00  inst_num_eq_res_simplified:             0
% 2.96/1.00  inst_num_child_elim:                    0
% 2.96/1.00  inst_num_of_dismatching_blockings:      352
% 2.96/1.00  inst_num_of_non_proper_insts:           1123
% 2.96/1.00  inst_num_of_duplicates:                 0
% 2.96/1.00  inst_inst_num_from_inst_to_res:         0
% 2.96/1.00  inst_dismatching_checking_time:         0.
% 2.96/1.00  
% 2.96/1.00  ------ Resolution
% 2.96/1.00  
% 2.96/1.00  res_num_of_clauses:                     0
% 2.96/1.00  res_num_in_passive:                     0
% 2.96/1.00  res_num_in_active:                      0
% 2.96/1.00  res_num_of_loops:                       149
% 2.96/1.00  res_forward_subset_subsumed:            179
% 2.96/1.00  res_backward_subset_subsumed:           2
% 2.96/1.00  res_forward_subsumed:                   0
% 2.96/1.00  res_backward_subsumed:                  0
% 2.96/1.00  res_forward_subsumption_resolution:     0
% 2.96/1.00  res_backward_subsumption_resolution:    0
% 2.96/1.00  res_clause_to_clause_subsumption:       501
% 2.96/1.00  res_orphan_elimination:                 0
% 2.96/1.00  res_tautology_del:                      168
% 2.96/1.00  res_num_eq_res_simplified:              0
% 2.96/1.00  res_num_sel_changes:                    0
% 2.96/1.00  res_moves_from_active_to_pass:          0
% 2.96/1.00  
% 2.96/1.00  ------ Superposition
% 2.96/1.00  
% 2.96/1.00  sup_time_total:                         0.
% 2.96/1.00  sup_time_generating:                    0.
% 2.96/1.00  sup_time_sim_full:                      0.
% 2.96/1.00  sup_time_sim_immed:                     0.
% 2.96/1.00  
% 2.96/1.00  sup_num_of_clauses:                     89
% 2.96/1.00  sup_num_in_active:                      74
% 2.96/1.00  sup_num_in_passive:                     15
% 2.96/1.00  sup_num_of_loops:                       81
% 2.96/1.00  sup_fw_superposition:                   77
% 2.96/1.00  sup_bw_superposition:                   63
% 2.96/1.00  sup_immediate_simplified:               33
% 2.96/1.00  sup_given_eliminated:                   0
% 2.96/1.00  comparisons_done:                       0
% 2.96/1.00  comparisons_avoided:                    0
% 2.96/1.00  
% 2.96/1.00  ------ Simplifications
% 2.96/1.00  
% 2.96/1.00  
% 2.96/1.00  sim_fw_subset_subsumed:                 14
% 2.96/1.00  sim_bw_subset_subsumed:                 4
% 2.96/1.00  sim_fw_subsumed:                        11
% 2.96/1.00  sim_bw_subsumed:                        3
% 2.96/1.00  sim_fw_subsumption_res:                 2
% 2.96/1.00  sim_bw_subsumption_res:                 0
% 2.96/1.00  sim_tautology_del:                      20
% 2.96/1.00  sim_eq_tautology_del:                   5
% 2.96/1.00  sim_eq_res_simp:                        1
% 2.96/1.00  sim_fw_demodulated:                     1
% 2.96/1.00  sim_bw_demodulated:                     7
% 2.96/1.00  sim_light_normalised:                   16
% 2.96/1.00  sim_joinable_taut:                      0
% 2.96/1.00  sim_joinable_simp:                      0
% 2.96/1.00  sim_ac_normalised:                      0
% 2.96/1.00  sim_smt_subsumption:                    0
% 2.96/1.00  
%------------------------------------------------------------------------------
