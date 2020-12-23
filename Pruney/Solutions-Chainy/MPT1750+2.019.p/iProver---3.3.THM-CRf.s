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
% DateTime   : Thu Dec  3 12:22:25 EST 2020

% Result     : Theorem 7.85s
% Output     : CNFRefutation 7.85s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 717 expanded)
%              Number of clauses        :  114 ( 224 expanded)
%              Number of leaves         :   26 ( 210 expanded)
%              Depth                    :   16
%              Number of atoms          :  778 (5498 expanded)
%              Number of equality atoms :  231 ( 819 expanded)
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

fof(f47,plain,(
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

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f57,plain,(
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

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f58,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f57,f56,f55,f54])).

fof(f89,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f87,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f81,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f99,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f78])).

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

fof(f36,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f73,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f58])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f90,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f15,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f41])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f82,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f83,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f84,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f85,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f91,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f58])).

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

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f39])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f97,plain,(
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
    inference(equality_resolution,[],[f76])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f94,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1477,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1483,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1498,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2454,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_1498])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1501,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7725,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2454,c_1501])).

cnf(c_9288,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2454,c_7725])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_78,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_15757,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9288,c_78,c_2454,c_7725])).

cnf(c_15758,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_15757])).

cnf(c_15767,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_pre_topc(sK1,sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1477,c_15758])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_40,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_41,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_12,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_75,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_77,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1824,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1825,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1824])).

cnf(c_1827,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1825])).

cnf(c_2165,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_11,c_28])).

cnf(c_2166,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2165])).

cnf(c_24,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_15,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1487,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4617,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_1487])).

cnf(c_4655,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4617])).

cnf(c_22,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1482,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_20,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_14,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_358,plain,
    ( ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_14])).

cnf(c_359,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(renaming,[status(thm)],[c_358])).

cnf(c_1469,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_1491,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1626,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1469,c_1491])).

cnf(c_6624,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1482,c_1626])).

cnf(c_6669,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6624])).

cnf(c_16154,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15767,c_40,c_41,c_77,c_1827,c_2166,c_4655,c_6669])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1480,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1494,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5543,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_1494])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1886,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1973,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1886])).

cnf(c_5860,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5543,c_27,c_25,c_1973])).

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
    inference(cnf_transformation,[],[f77])).

cnf(c_1484,plain,
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

cnf(c_3140,plain,
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
    inference(superposition,[status(thm)],[c_1480,c_1484])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_36,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_37,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_38,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_39,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_44,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_45,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3772,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3140,c_36,c_37,c_38,c_39,c_40,c_41,c_44,c_45])).

cnf(c_3773,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3772])).

cnf(c_3782,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1477,c_3773])).

cnf(c_5866,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(demodulation,[status(thm)],[c_5860,c_3782])).

cnf(c_16158,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK1)) ),
    inference(demodulation,[status(thm)],[c_16154,c_5866])).

cnf(c_7,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1495,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3331,plain,
    ( v4_relat_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_1495])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1497,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4265,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3331,c_1497])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1816,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1830,plain,
    ( v4_relat_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1954,plain,
    ( ~ v4_relat_1(sK3,X0)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2245,plain,
    ( ~ v4_relat_1(sK3,u1_struct_0(sK1))
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
    inference(instantiation,[status(thm)],[c_1954])).

cnf(c_5040,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4265,c_25,c_1816,c_1830,c_2245])).

cnf(c_16163,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_16158,c_5040])).

cnf(c_654,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | r1_funct_2(X6,X7,X8,X9,X10,X11)
    | X8 != X2
    | X6 != X0
    | X7 != X1
    | X9 != X3
    | X10 != X4
    | X11 != X5 ),
    theory(equality)).

cnf(c_3245,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ r1_funct_2(u1_struct_0(X6),u1_struct_0(sK0),u1_struct_0(X7),u1_struct_0(sK0),sK3,sK3)
    | X0 != u1_struct_0(X6)
    | X2 != u1_struct_0(X7)
    | X1 != u1_struct_0(sK0)
    | X3 != u1_struct_0(sK0)
    | X4 != sK3
    | X5 != sK3 ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_4593,plain,
    ( r1_funct_2(X0,X1,X2,u1_struct_0(sK0),X3,X4)
    | ~ r1_funct_2(u1_struct_0(X5),u1_struct_0(sK0),u1_struct_0(X6),u1_struct_0(sK0),sK3,sK3)
    | X2 != u1_struct_0(X6)
    | X0 != u1_struct_0(X5)
    | X1 != u1_struct_0(sK0)
    | X4 != sK3
    | X3 != sK3
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3245])).

cnf(c_7145,plain,
    ( r1_funct_2(X0,X1,X2,u1_struct_0(sK0),sK3,X3)
    | ~ r1_funct_2(u1_struct_0(X4),u1_struct_0(sK0),u1_struct_0(X5),u1_struct_0(sK0),sK3,sK3)
    | X2 != u1_struct_0(X5)
    | X0 != u1_struct_0(X4)
    | X1 != u1_struct_0(sK0)
    | X3 != sK3
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4593])).

cnf(c_8754,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(sK0),sK3,sK3)
    | r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(sK2) != u1_struct_0(X1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(X0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_7145])).

cnf(c_8756,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    | ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(sK2) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_8754])).

cnf(c_639,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2354,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_1472,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_10,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1492,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2252,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1472,c_1492])).

cnf(c_2258,plain,
    ( l1_struct_0(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2252])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2230,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_16,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1896,plain,
    ( r1_funct_2(X0,X1,X2,X3,sK3,sK3)
    | ~ v1_funct_2(sK3,X2,X3)
    | ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2016,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,X1,sK3,sK3)
    | ~ v1_funct_2(sK3,X0,X1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(X1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1896])).

cnf(c_2084,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2016])).

cnf(c_1981,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_650,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_666,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_650])).

cnf(c_108,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_104,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_23,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16163,c_15767,c_8756,c_6669,c_4655,c_2354,c_2258,c_2230,c_2166,c_2084,c_1981,c_1827,c_666,c_108,c_104,c_77,c_23,c_25,c_26,c_27,c_41,c_40,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:19:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.85/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.85/1.49  
% 7.85/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.85/1.49  
% 7.85/1.49  ------  iProver source info
% 7.85/1.49  
% 7.85/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.85/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.85/1.49  git: non_committed_changes: false
% 7.85/1.49  git: last_make_outside_of_git: false
% 7.85/1.49  
% 7.85/1.49  ------ 
% 7.85/1.49  ------ Parsing...
% 7.85/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.85/1.49  
% 7.85/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.85/1.49  
% 7.85/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.85/1.49  
% 7.85/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.85/1.49  ------ Proving...
% 7.85/1.49  ------ Problem Properties 
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  clauses                                 35
% 7.85/1.49  conjectures                             13
% 7.85/1.49  EPR                                     14
% 7.85/1.49  Horn                                    32
% 7.85/1.49  unary                                   14
% 7.85/1.49  binary                                  8
% 7.85/1.49  lits                                    94
% 7.85/1.49  lits eq                                 6
% 7.85/1.49  fd_pure                                 0
% 7.85/1.49  fd_pseudo                               0
% 7.85/1.49  fd_cond                                 0
% 7.85/1.49  fd_pseudo_cond                          2
% 7.85/1.49  AC symbols                              0
% 7.85/1.49  
% 7.85/1.49  ------ Input Options Time Limit: Unbounded
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  ------ 
% 7.85/1.49  Current options:
% 7.85/1.49  ------ 
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  ------ Proving...
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  % SZS status Theorem for theBenchmark.p
% 7.85/1.49  
% 7.85/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.85/1.49  
% 7.85/1.49  fof(f19,conjecture,(
% 7.85/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f20,negated_conjecture,(
% 7.85/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 7.85/1.49    inference(negated_conjecture,[],[f19])).
% 7.85/1.49  
% 7.85/1.49  fof(f47,plain,(
% 7.85/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.85/1.49    inference(ennf_transformation,[],[f20])).
% 7.85/1.49  
% 7.85/1.49  fof(f48,plain,(
% 7.85/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.85/1.49    inference(flattening,[],[f47])).
% 7.85/1.49  
% 7.85/1.49  fof(f57,plain,(
% 7.85/1.49    ( ! [X2,X0,X1] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 7.85/1.49    introduced(choice_axiom,[])).
% 7.85/1.49  
% 7.85/1.49  fof(f56,plain,(
% 7.85/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 7.85/1.49    introduced(choice_axiom,[])).
% 7.85/1.49  
% 7.85/1.49  fof(f55,plain,(
% 7.85/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 7.85/1.49    introduced(choice_axiom,[])).
% 7.85/1.49  
% 7.85/1.49  fof(f54,plain,(
% 7.85/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.85/1.49    introduced(choice_axiom,[])).
% 7.85/1.49  
% 7.85/1.49  fof(f58,plain,(
% 7.85/1.49    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.85/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f57,f56,f55,f54])).
% 7.85/1.49  
% 7.85/1.49  fof(f89,plain,(
% 7.85/1.49    m1_pre_topc(sK2,sK1)),
% 7.85/1.49    inference(cnf_transformation,[],[f58])).
% 7.85/1.49  
% 7.85/1.49  fof(f17,axiom,(
% 7.85/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f45,plain,(
% 7.85/1.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f17])).
% 7.85/1.49  
% 7.85/1.49  fof(f80,plain,(
% 7.85/1.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f45])).
% 7.85/1.49  
% 7.85/1.49  fof(f2,axiom,(
% 7.85/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f51,plain,(
% 7.85/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.85/1.49    inference(nnf_transformation,[],[f2])).
% 7.85/1.49  
% 7.85/1.49  fof(f62,plain,(
% 7.85/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.85/1.49    inference(cnf_transformation,[],[f51])).
% 7.85/1.49  
% 7.85/1.49  fof(f1,axiom,(
% 7.85/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f49,plain,(
% 7.85/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.85/1.49    inference(nnf_transformation,[],[f1])).
% 7.85/1.49  
% 7.85/1.49  fof(f50,plain,(
% 7.85/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.85/1.49    inference(flattening,[],[f49])).
% 7.85/1.49  
% 7.85/1.49  fof(f61,plain,(
% 7.85/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f50])).
% 7.85/1.49  
% 7.85/1.49  fof(f9,axiom,(
% 7.85/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f32,plain,(
% 7.85/1.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f9])).
% 7.85/1.49  
% 7.85/1.49  fof(f70,plain,(
% 7.85/1.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f32])).
% 7.85/1.49  
% 7.85/1.49  fof(f86,plain,(
% 7.85/1.49    v2_pre_topc(sK1)),
% 7.85/1.49    inference(cnf_transformation,[],[f58])).
% 7.85/1.49  
% 7.85/1.49  fof(f87,plain,(
% 7.85/1.49    l1_pre_topc(sK1)),
% 7.85/1.49    inference(cnf_transformation,[],[f58])).
% 7.85/1.49  
% 7.85/1.49  fof(f10,axiom,(
% 7.85/1.49    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f33,plain,(
% 7.85/1.49    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f10])).
% 7.85/1.49  
% 7.85/1.49  fof(f71,plain,(
% 7.85/1.49    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f33])).
% 7.85/1.49  
% 7.85/1.49  fof(f7,axiom,(
% 7.85/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f22,plain,(
% 7.85/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 7.85/1.49    inference(pure_predicate_removal,[],[f7])).
% 7.85/1.49  
% 7.85/1.49  fof(f30,plain,(
% 7.85/1.49    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.85/1.49    inference(ennf_transformation,[],[f22])).
% 7.85/1.49  
% 7.85/1.49  fof(f68,plain,(
% 7.85/1.49    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.85/1.49    inference(cnf_transformation,[],[f30])).
% 7.85/1.49  
% 7.85/1.49  fof(f93,plain,(
% 7.85/1.49    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 7.85/1.49    inference(cnf_transformation,[],[f58])).
% 7.85/1.49  
% 7.85/1.49  fof(f13,axiom,(
% 7.85/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f38,plain,(
% 7.85/1.49    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f13])).
% 7.85/1.49  
% 7.85/1.49  fof(f74,plain,(
% 7.85/1.49    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f38])).
% 7.85/1.49  
% 7.85/1.49  fof(f18,axiom,(
% 7.85/1.49    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f46,plain,(
% 7.85/1.49    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f18])).
% 7.85/1.49  
% 7.85/1.49  fof(f81,plain,(
% 7.85/1.49    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f46])).
% 7.85/1.49  
% 7.85/1.49  fof(f16,axiom,(
% 7.85/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f43,plain,(
% 7.85/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f16])).
% 7.85/1.49  
% 7.85/1.49  fof(f44,plain,(
% 7.85/1.49    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(flattening,[],[f43])).
% 7.85/1.49  
% 7.85/1.49  fof(f53,plain,(
% 7.85/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(nnf_transformation,[],[f44])).
% 7.85/1.49  
% 7.85/1.49  fof(f78,plain,(
% 7.85/1.49    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f53])).
% 7.85/1.49  
% 7.85/1.49  fof(f99,plain,(
% 7.85/1.49    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(equality_resolution,[],[f78])).
% 7.85/1.49  
% 7.85/1.49  fof(f12,axiom,(
% 7.85/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f21,plain,(
% 7.85/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 7.85/1.49    inference(pure_predicate_removal,[],[f12])).
% 7.85/1.49  
% 7.85/1.49  fof(f36,plain,(
% 7.85/1.49    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.85/1.49    inference(ennf_transformation,[],[f21])).
% 7.85/1.49  
% 7.85/1.49  fof(f37,plain,(
% 7.85/1.49    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.85/1.49    inference(flattening,[],[f36])).
% 7.85/1.49  
% 7.85/1.49  fof(f73,plain,(
% 7.85/1.49    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f37])).
% 7.85/1.49  
% 7.85/1.49  fof(f92,plain,(
% 7.85/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 7.85/1.49    inference(cnf_transformation,[],[f58])).
% 7.85/1.49  
% 7.85/1.49  fof(f6,axiom,(
% 7.85/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f28,plain,(
% 7.85/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.85/1.49    inference(ennf_transformation,[],[f6])).
% 7.85/1.49  
% 7.85/1.49  fof(f29,plain,(
% 7.85/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.85/1.49    inference(flattening,[],[f28])).
% 7.85/1.49  
% 7.85/1.49  fof(f67,plain,(
% 7.85/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f29])).
% 7.85/1.49  
% 7.85/1.49  fof(f90,plain,(
% 7.85/1.49    v1_funct_1(sK3)),
% 7.85/1.49    inference(cnf_transformation,[],[f58])).
% 7.85/1.49  
% 7.85/1.49  fof(f15,axiom,(
% 7.85/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f41,plain,(
% 7.85/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.85/1.49    inference(ennf_transformation,[],[f15])).
% 7.85/1.49  
% 7.85/1.49  fof(f42,plain,(
% 7.85/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.85/1.49    inference(flattening,[],[f41])).
% 7.85/1.49  
% 7.85/1.49  fof(f77,plain,(
% 7.85/1.49    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f42])).
% 7.85/1.49  
% 7.85/1.49  fof(f82,plain,(
% 7.85/1.49    ~v2_struct_0(sK0)),
% 7.85/1.49    inference(cnf_transformation,[],[f58])).
% 7.85/1.49  
% 7.85/1.49  fof(f83,plain,(
% 7.85/1.49    v2_pre_topc(sK0)),
% 7.85/1.49    inference(cnf_transformation,[],[f58])).
% 7.85/1.49  
% 7.85/1.49  fof(f84,plain,(
% 7.85/1.49    l1_pre_topc(sK0)),
% 7.85/1.49    inference(cnf_transformation,[],[f58])).
% 7.85/1.49  
% 7.85/1.49  fof(f85,plain,(
% 7.85/1.49    ~v2_struct_0(sK1)),
% 7.85/1.49    inference(cnf_transformation,[],[f58])).
% 7.85/1.49  
% 7.85/1.49  fof(f91,plain,(
% 7.85/1.49    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 7.85/1.49    inference(cnf_transformation,[],[f58])).
% 7.85/1.49  
% 7.85/1.49  fof(f5,axiom,(
% 7.85/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f23,plain,(
% 7.85/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.85/1.49    inference(pure_predicate_removal,[],[f5])).
% 7.85/1.49  
% 7.85/1.49  fof(f27,plain,(
% 7.85/1.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.85/1.49    inference(ennf_transformation,[],[f23])).
% 7.85/1.49  
% 7.85/1.49  fof(f66,plain,(
% 7.85/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.85/1.49    inference(cnf_transformation,[],[f27])).
% 7.85/1.49  
% 7.85/1.49  fof(f3,axiom,(
% 7.85/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f24,plain,(
% 7.85/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.85/1.49    inference(ennf_transformation,[],[f3])).
% 7.85/1.49  
% 7.85/1.49  fof(f25,plain,(
% 7.85/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.85/1.49    inference(flattening,[],[f24])).
% 7.85/1.49  
% 7.85/1.49  fof(f64,plain,(
% 7.85/1.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f25])).
% 7.85/1.49  
% 7.85/1.49  fof(f4,axiom,(
% 7.85/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f26,plain,(
% 7.85/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.85/1.49    inference(ennf_transformation,[],[f4])).
% 7.85/1.49  
% 7.85/1.49  fof(f65,plain,(
% 7.85/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.85/1.49    inference(cnf_transformation,[],[f26])).
% 7.85/1.49  
% 7.85/1.49  fof(f8,axiom,(
% 7.85/1.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f31,plain,(
% 7.85/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f8])).
% 7.85/1.49  
% 7.85/1.49  fof(f69,plain,(
% 7.85/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f31])).
% 7.85/1.49  
% 7.85/1.49  fof(f11,axiom,(
% 7.85/1.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f34,plain,(
% 7.85/1.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.85/1.49    inference(ennf_transformation,[],[f11])).
% 7.85/1.49  
% 7.85/1.49  fof(f35,plain,(
% 7.85/1.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.85/1.49    inference(flattening,[],[f34])).
% 7.85/1.49  
% 7.85/1.49  fof(f72,plain,(
% 7.85/1.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f35])).
% 7.85/1.49  
% 7.85/1.49  fof(f14,axiom,(
% 7.85/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f39,plain,(
% 7.85/1.49    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 7.85/1.49    inference(ennf_transformation,[],[f14])).
% 7.85/1.49  
% 7.85/1.49  fof(f40,plain,(
% 7.85/1.49    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 7.85/1.49    inference(flattening,[],[f39])).
% 7.85/1.49  
% 7.85/1.49  fof(f52,plain,(
% 7.85/1.49    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 7.85/1.49    inference(nnf_transformation,[],[f40])).
% 7.85/1.49  
% 7.85/1.49  fof(f76,plain,(
% 7.85/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f52])).
% 7.85/1.49  
% 7.85/1.49  fof(f97,plain,(
% 7.85/1.49    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 7.85/1.49    inference(equality_resolution,[],[f76])).
% 7.85/1.49  
% 7.85/1.49  fof(f59,plain,(
% 7.85/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.85/1.49    inference(cnf_transformation,[],[f50])).
% 7.85/1.49  
% 7.85/1.49  fof(f96,plain,(
% 7.85/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.85/1.49    inference(equality_resolution,[],[f59])).
% 7.85/1.49  
% 7.85/1.49  fof(f94,plain,(
% 7.85/1.49    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 7.85/1.49    inference(cnf_transformation,[],[f58])).
% 7.85/1.49  
% 7.85/1.49  cnf(c_28,negated_conjecture,
% 7.85/1.49      ( m1_pre_topc(sK2,sK1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1477,plain,
% 7.85/1.49      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_21,plain,
% 7.85/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.85/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.85/1.49      | ~ l1_pre_topc(X1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1483,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_4,plain,
% 7.85/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1498,plain,
% 7.85/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.85/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2454,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_1483,c_1498]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_0,plain,
% 7.85/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.85/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1501,plain,
% 7.85/1.49      ( X0 = X1
% 7.85/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.85/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_7725,plain,
% 7.85/1.49      ( u1_struct_0(X0) = u1_struct_0(X1)
% 7.85/1.49      | m1_pre_topc(X1,X0) != iProver_top
% 7.85/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 7.85/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_2454,c_1501]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_9288,plain,
% 7.85/1.49      ( u1_struct_0(X0) = u1_struct_0(X1)
% 7.85/1.49      | m1_pre_topc(X1,X0) != iProver_top
% 7.85/1.49      | m1_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top
% 7.85/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_2454,c_7725]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_11,plain,
% 7.85/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.85/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_78,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top
% 7.85/1.49      | l1_pre_topc(X0) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_15757,plain,
% 7.85/1.49      ( l1_pre_topc(X1) != iProver_top
% 7.85/1.49      | m1_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | m1_pre_topc(X1,X0) != iProver_top
% 7.85/1.49      | u1_struct_0(X0) = u1_struct_0(X1) ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_9288,c_78,c_2454,c_7725]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_15758,plain,
% 7.85/1.49      ( u1_struct_0(X0) = u1_struct_0(X1)
% 7.85/1.49      | m1_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | m1_pre_topc(X1,X0) != iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.85/1.49      inference(renaming,[status(thm)],[c_15757]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_15767,plain,
% 7.85/1.49      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 7.85/1.49      | m1_pre_topc(sK1,sK2) != iProver_top
% 7.85/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_1477,c_15758]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_31,negated_conjecture,
% 7.85/1.49      ( v2_pre_topc(sK1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_40,plain,
% 7.85/1.49      ( v2_pre_topc(sK1) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_30,negated_conjecture,
% 7.85/1.49      ( l1_pre_topc(sK1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_41,plain,
% 7.85/1.49      ( l1_pre_topc(sK1) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_12,plain,
% 7.85/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.85/1.49      | ~ l1_pre_topc(X0) ),
% 7.85/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_75,plain,
% 7.85/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 7.85/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_77,plain,
% 7.85/1.49      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 7.85/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_75]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_9,plain,
% 7.85/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.85/1.49      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 7.85/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1824,plain,
% 7.85/1.49      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.85/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1825,plain,
% 7.85/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 7.85/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_1824]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1827,plain,
% 7.85/1.49      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 7.85/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_1825]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2165,plain,
% 7.85/1.49      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK1) ),
% 7.85/1.49      inference(resolution,[status(thm)],[c_11,c_28]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2166,plain,
% 7.85/1.49      ( l1_pre_topc(sK2) = iProver_top
% 7.85/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_2165]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_24,negated_conjecture,
% 7.85/1.49      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 7.85/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_15,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1)
% 7.85/1.49      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.85/1.49      | ~ l1_pre_topc(X1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1487,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1) = iProver_top
% 7.85/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_4617,plain,
% 7.85/1.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.85/1.49      | m1_pre_topc(X0,sK2) = iProver_top
% 7.85/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_24,c_1487]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_4655,plain,
% 7.85/1.49      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.85/1.49      | m1_pre_topc(sK1,sK2) = iProver_top
% 7.85/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_4617]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_22,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.85/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1482,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X0) = iProver_top
% 7.85/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_20,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1)
% 7.85/1.49      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.85/1.49      | ~ v2_pre_topc(X0)
% 7.85/1.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.85/1.49      | ~ l1_pre_topc(X1)
% 7.85/1.49      | ~ l1_pre_topc(X0)
% 7.85/1.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 7.85/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_14,plain,
% 7.85/1.49      ( ~ v2_pre_topc(X0)
% 7.85/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.85/1.49      | ~ l1_pre_topc(X0) ),
% 7.85/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_358,plain,
% 7.85/1.49      ( ~ v2_pre_topc(X0)
% 7.85/1.49      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.85/1.49      | m1_pre_topc(X0,X1)
% 7.85/1.49      | ~ l1_pre_topc(X1)
% 7.85/1.49      | ~ l1_pre_topc(X0)
% 7.85/1.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_20,c_14]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_359,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1)
% 7.85/1.49      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.85/1.49      | ~ v2_pre_topc(X0)
% 7.85/1.49      | ~ l1_pre_topc(X0)
% 7.85/1.49      | ~ l1_pre_topc(X1)
% 7.85/1.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 7.85/1.49      inference(renaming,[status(thm)],[c_358]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1469,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1) = iProver_top
% 7.85/1.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 7.85/1.49      | v2_pre_topc(X0) != iProver_top
% 7.85/1.49      | l1_pre_topc(X0) != iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top
% 7.85/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_359]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1491,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top
% 7.85/1.49      | l1_pre_topc(X0) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1626,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1) = iProver_top
% 7.85/1.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 7.85/1.49      | v2_pre_topc(X0) != iProver_top
% 7.85/1.49      | l1_pre_topc(X0) != iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.85/1.49      inference(forward_subsumption_resolution,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_1469,c_1491]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_6624,plain,
% 7.85/1.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 7.85/1.49      | v2_pre_topc(X0) != iProver_top
% 7.85/1.49      | l1_pre_topc(X0) != iProver_top
% 7.85/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_1482,c_1626]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_6669,plain,
% 7.85/1.49      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.85/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.85/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.85/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_6624]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_16154,plain,
% 7.85/1.49      ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_15767,c_40,c_41,c_77,c_1827,c_2166,c_4655,c_6669]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_25,negated_conjecture,
% 7.85/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 7.85/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1480,plain,
% 7.85/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_8,plain,
% 7.85/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.85/1.49      | ~ v1_funct_1(X0)
% 7.85/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.85/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1494,plain,
% 7.85/1.49      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 7.85/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.85/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_5543,plain,
% 7.85/1.49      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0)
% 7.85/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_1480,c_1494]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_27,negated_conjecture,
% 7.85/1.49      ( v1_funct_1(sK3) ),
% 7.85/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1886,plain,
% 7.85/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.85/1.49      | ~ v1_funct_1(sK3)
% 7.85/1.49      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1973,plain,
% 7.85/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.85/1.49      | ~ v1_funct_1(sK3)
% 7.85/1.49      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_1886]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_5860,plain,
% 7.85/1.49      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_5543,c_27,c_25,c_1973]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_18,plain,
% 7.85/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.85/1.49      | ~ m1_pre_topc(X3,X1)
% 7.85/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.85/1.49      | ~ v2_pre_topc(X1)
% 7.85/1.49      | ~ v2_pre_topc(X2)
% 7.85/1.49      | v2_struct_0(X1)
% 7.85/1.49      | v2_struct_0(X2)
% 7.85/1.49      | ~ l1_pre_topc(X1)
% 7.85/1.49      | ~ l1_pre_topc(X2)
% 7.85/1.49      | ~ v1_funct_1(X0)
% 7.85/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 7.85/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1484,plain,
% 7.85/1.49      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
% 7.85/1.49      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 7.85/1.49      | m1_pre_topc(X3,X0) != iProver_top
% 7.85/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 7.85/1.49      | v2_pre_topc(X0) != iProver_top
% 7.85/1.49      | v2_pre_topc(X1) != iProver_top
% 7.85/1.49      | v2_struct_0(X0) = iProver_top
% 7.85/1.49      | v2_struct_0(X1) = iProver_top
% 7.85/1.49      | l1_pre_topc(X0) != iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top
% 7.85/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_3140,plain,
% 7.85/1.49      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 7.85/1.49      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 7.85/1.49      | m1_pre_topc(X0,sK1) != iProver_top
% 7.85/1.49      | v2_pre_topc(sK0) != iProver_top
% 7.85/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.85/1.49      | v2_struct_0(sK0) = iProver_top
% 7.85/1.49      | v2_struct_0(sK1) = iProver_top
% 7.85/1.49      | l1_pre_topc(sK0) != iProver_top
% 7.85/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.85/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_1480,c_1484]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_35,negated_conjecture,
% 7.85/1.49      ( ~ v2_struct_0(sK0) ),
% 7.85/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_36,plain,
% 7.85/1.49      ( v2_struct_0(sK0) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_34,negated_conjecture,
% 7.85/1.49      ( v2_pre_topc(sK0) ),
% 7.85/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_37,plain,
% 7.85/1.49      ( v2_pre_topc(sK0) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_33,negated_conjecture,
% 7.85/1.49      ( l1_pre_topc(sK0) ),
% 7.85/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_38,plain,
% 7.85/1.49      ( l1_pre_topc(sK0) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_32,negated_conjecture,
% 7.85/1.49      ( ~ v2_struct_0(sK1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_39,plain,
% 7.85/1.49      ( v2_struct_0(sK1) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_44,plain,
% 7.85/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_26,negated_conjecture,
% 7.85/1.49      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 7.85/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_45,plain,
% 7.85/1.49      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_3772,plain,
% 7.85/1.49      ( m1_pre_topc(X0,sK1) != iProver_top
% 7.85/1.49      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0) ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_3140,c_36,c_37,c_38,c_39,c_40,c_41,c_44,c_45]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_3773,plain,
% 7.85/1.49      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 7.85/1.49      | m1_pre_topc(X0,sK1) != iProver_top ),
% 7.85/1.49      inference(renaming,[status(thm)],[c_3772]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_3782,plain,
% 7.85/1.49      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_1477,c_3773]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_5866,plain,
% 7.85/1.49      ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 7.85/1.49      inference(demodulation,[status(thm)],[c_5860,c_3782]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_16158,plain,
% 7.85/1.49      ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK1)) ),
% 7.85/1.49      inference(demodulation,[status(thm)],[c_16154,c_5866]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_7,plain,
% 7.85/1.49      ( v4_relat_1(X0,X1)
% 7.85/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.85/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1495,plain,
% 7.85/1.49      ( v4_relat_1(X0,X1) = iProver_top
% 7.85/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_3331,plain,
% 7.85/1.49      ( v4_relat_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_1480,c_1495]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_5,plain,
% 7.85/1.49      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.85/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1497,plain,
% 7.85/1.49      ( k7_relat_1(X0,X1) = X0
% 7.85/1.49      | v4_relat_1(X0,X1) != iProver_top
% 7.85/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_4265,plain,
% 7.85/1.49      ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3
% 7.85/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_3331,c_1497]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_6,plain,
% 7.85/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.85/1.49      | v1_relat_1(X0) ),
% 7.85/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1816,plain,
% 7.85/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.85/1.49      | v1_relat_1(sK3) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1830,plain,
% 7.85/1.49      ( v4_relat_1(sK3,u1_struct_0(sK1))
% 7.85/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1954,plain,
% 7.85/1.49      ( ~ v4_relat_1(sK3,X0)
% 7.85/1.49      | ~ v1_relat_1(sK3)
% 7.85/1.49      | k7_relat_1(sK3,X0) = sK3 ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2245,plain,
% 7.85/1.49      ( ~ v4_relat_1(sK3,u1_struct_0(sK1))
% 7.85/1.49      | ~ v1_relat_1(sK3)
% 7.85/1.49      | k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_1954]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_5040,plain,
% 7.85/1.49      ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_4265,c_25,c_1816,c_1830,c_2245]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_16163,plain,
% 7.85/1.49      ( k2_tmap_1(sK1,sK0,sK3,sK2) = sK3 ),
% 7.85/1.49      inference(light_normalisation,[status(thm)],[c_16158,c_5040]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_654,plain,
% 7.85/1.49      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 7.85/1.49      | r1_funct_2(X6,X7,X8,X9,X10,X11)
% 7.85/1.49      | X8 != X2
% 7.85/1.49      | X6 != X0
% 7.85/1.49      | X7 != X1
% 7.85/1.49      | X9 != X3
% 7.85/1.49      | X10 != X4
% 7.85/1.49      | X11 != X5 ),
% 7.85/1.49      theory(equality) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_3245,plain,
% 7.85/1.49      ( r1_funct_2(X0,X1,X2,X3,X4,X5)
% 7.85/1.49      | ~ r1_funct_2(u1_struct_0(X6),u1_struct_0(sK0),u1_struct_0(X7),u1_struct_0(sK0),sK3,sK3)
% 7.85/1.49      | X0 != u1_struct_0(X6)
% 7.85/1.49      | X2 != u1_struct_0(X7)
% 7.85/1.49      | X1 != u1_struct_0(sK0)
% 7.85/1.49      | X3 != u1_struct_0(sK0)
% 7.85/1.49      | X4 != sK3
% 7.85/1.49      | X5 != sK3 ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_654]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_4593,plain,
% 7.85/1.49      ( r1_funct_2(X0,X1,X2,u1_struct_0(sK0),X3,X4)
% 7.85/1.49      | ~ r1_funct_2(u1_struct_0(X5),u1_struct_0(sK0),u1_struct_0(X6),u1_struct_0(sK0),sK3,sK3)
% 7.85/1.49      | X2 != u1_struct_0(X6)
% 7.85/1.49      | X0 != u1_struct_0(X5)
% 7.85/1.49      | X1 != u1_struct_0(sK0)
% 7.85/1.49      | X4 != sK3
% 7.85/1.49      | X3 != sK3
% 7.85/1.49      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_3245]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_7145,plain,
% 7.85/1.49      ( r1_funct_2(X0,X1,X2,u1_struct_0(sK0),sK3,X3)
% 7.85/1.49      | ~ r1_funct_2(u1_struct_0(X4),u1_struct_0(sK0),u1_struct_0(X5),u1_struct_0(sK0),sK3,sK3)
% 7.85/1.49      | X2 != u1_struct_0(X5)
% 7.85/1.49      | X0 != u1_struct_0(X4)
% 7.85/1.49      | X1 != u1_struct_0(sK0)
% 7.85/1.49      | X3 != sK3
% 7.85/1.49      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 7.85/1.49      | sK3 != sK3 ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_4593]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_8754,plain,
% 7.85/1.49      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(sK0),sK3,sK3)
% 7.85/1.49      | r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
% 7.85/1.49      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 7.85/1.49      | u1_struct_0(sK2) != u1_struct_0(X1)
% 7.85/1.49      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 7.85/1.49      | u1_struct_0(sK1) != u1_struct_0(X0)
% 7.85/1.49      | sK3 != sK3 ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_7145]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_8756,plain,
% 7.85/1.49      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
% 7.85/1.49      | ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
% 7.85/1.49      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 7.85/1.49      | u1_struct_0(sK2) != u1_struct_0(sK1)
% 7.85/1.49      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 7.85/1.49      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 7.85/1.49      | sK3 != sK3 ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_8754]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_639,plain,( X0 = X0 ),theory(equality) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2354,plain,
% 7.85/1.49      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_639]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1472,plain,
% 7.85/1.49      ( l1_pre_topc(sK0) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_10,plain,
% 7.85/1.49      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.85/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1492,plain,
% 7.85/1.49      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2252,plain,
% 7.85/1.49      ( l1_struct_0(sK0) = iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_1472,c_1492]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2258,plain,
% 7.85/1.49      ( l1_struct_0(sK0) ),
% 7.85/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_2252]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_13,plain,
% 7.85/1.49      ( v2_struct_0(X0)
% 7.85/1.49      | ~ v1_xboole_0(u1_struct_0(X0))
% 7.85/1.49      | ~ l1_struct_0(X0) ),
% 7.85/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2230,plain,
% 7.85/1.49      ( v2_struct_0(sK0)
% 7.85/1.49      | ~ v1_xboole_0(u1_struct_0(sK0))
% 7.85/1.49      | ~ l1_struct_0(sK0) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_16,plain,
% 7.85/1.49      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 7.85/1.49      | ~ v1_funct_2(X4,X2,X3)
% 7.85/1.49      | ~ v1_funct_2(X4,X0,X1)
% 7.85/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.85/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.85/1.49      | v1_xboole_0(X1)
% 7.85/1.49      | v1_xboole_0(X3)
% 7.85/1.49      | ~ v1_funct_1(X4) ),
% 7.85/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1896,plain,
% 7.85/1.49      ( r1_funct_2(X0,X1,X2,X3,sK3,sK3)
% 7.85/1.49      | ~ v1_funct_2(sK3,X2,X3)
% 7.85/1.49      | ~ v1_funct_2(sK3,X0,X1)
% 7.85/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.85/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.85/1.49      | v1_xboole_0(X1)
% 7.85/1.49      | v1_xboole_0(X3)
% 7.85/1.49      | ~ v1_funct_1(sK3) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2016,plain,
% 7.85/1.49      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,X1,sK3,sK3)
% 7.85/1.49      | ~ v1_funct_2(sK3,X0,X1)
% 7.85/1.49      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 7.85/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.85/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.85/1.49      | v1_xboole_0(X1)
% 7.85/1.49      | v1_xboole_0(u1_struct_0(sK0))
% 7.85/1.49      | ~ v1_funct_1(sK3) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_1896]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2084,plain,
% 7.85/1.49      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
% 7.85/1.49      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 7.85/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.85/1.49      | v1_xboole_0(u1_struct_0(sK0))
% 7.85/1.49      | ~ v1_funct_1(sK3) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_2016]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1981,plain,
% 7.85/1.49      ( sK3 = sK3 ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_639]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_650,plain,
% 7.85/1.49      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 7.85/1.49      theory(equality) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_666,plain,
% 7.85/1.49      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_650]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_108,plain,
% 7.85/1.49      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2,plain,
% 7.85/1.49      ( r1_tarski(X0,X0) ),
% 7.85/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_104,plain,
% 7.85/1.49      ( r1_tarski(sK1,sK1) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_23,negated_conjecture,
% 7.85/1.49      ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
% 7.85/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(contradiction,plain,
% 7.85/1.49      ( $false ),
% 7.85/1.49      inference(minisat,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_16163,c_15767,c_8756,c_6669,c_4655,c_2354,c_2258,
% 7.85/1.49                 c_2230,c_2166,c_2084,c_1981,c_1827,c_666,c_108,c_104,
% 7.85/1.49                 c_77,c_23,c_25,c_26,c_27,c_41,c_40,c_35]) ).
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.85/1.49  
% 7.85/1.49  ------                               Statistics
% 7.85/1.49  
% 7.85/1.49  ------ Selected
% 7.85/1.49  
% 7.85/1.49  total_time:                             0.82
% 7.85/1.49  
%------------------------------------------------------------------------------
