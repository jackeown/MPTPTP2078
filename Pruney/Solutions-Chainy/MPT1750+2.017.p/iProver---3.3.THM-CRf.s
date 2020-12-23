%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:25 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 529 expanded)
%              Number of clauses        :  101 ( 154 expanded)
%              Number of leaves         :   22 ( 163 expanded)
%              Depth                    :   20
%              Number of atoms          :  718 (4448 expanded)
%              Number of equality atoms :  211 ( 595 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f50,f49,f48,f47])).

fof(f81,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f85,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f51])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(flattening,[],[f35])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f75,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f76,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(flattening,[],[f33])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f89,plain,(
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
    inference(equality_resolution,[],[f70])).

fof(f86,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1644,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1648,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1653,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3876,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1648,c_1653])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1656,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6015,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3876,c_1656])).

cnf(c_6345,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3876,c_6015])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_70,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3708,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_20,c_4])).

cnf(c_3709,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3708])).

cnf(c_9219,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6345,c_70,c_3709,c_6015])).

cnf(c_9220,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9219])).

cnf(c_9229,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_pre_topc(sK1,sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1644,c_9220])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_40,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_21,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_47,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_49,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_62,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_64,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_2461,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_12,c_27])).

cnf(c_2462,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2461])).

cnf(c_23,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_14,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1649,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4005,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_1649])).

cnf(c_4020,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4005])).

cnf(c_9550,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9229,c_40,c_49,c_64,c_2462,c_4020])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1646,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f71])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_573,plain,
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
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_574,plain,
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
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_1634,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_2422,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1646,c_1634])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_610,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_1633,plain,
    ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_2243,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1646,c_1633])).

cnf(c_2423,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2422,c_2243])).

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

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_38,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_39,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_44,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2428,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2423,c_35,c_36,c_37,c_38,c_39,c_40,c_44])).

cnf(c_2436,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_1644,c_2428])).

cnf(c_11,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_440,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_11,c_13])).

cnf(c_17,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_22,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_498,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_499,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_531,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_440,c_499])).

cnf(c_621,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_26,c_531])).

cnf(c_918,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | sP0_iProver_split
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_621])).

cnf(c_1631,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_918])).

cnf(c_2561,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2436,c_1631])).

cnf(c_917,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_621])).

cnf(c_920,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2254,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ sP0_iProver_split ),
    inference(resolution,[status(thm)],[c_917,c_920])).

cnf(c_2255,plain,
    ( v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2254])).

cnf(c_2564,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2561,c_35,c_37,c_2255])).

cnf(c_2565,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2564])).

cnf(c_9553,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9550,c_2565])).

cnf(c_9,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_9,c_6])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_462,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_8])).

cnf(c_463,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_462])).

cnf(c_1635,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_2708,plain,
    ( r1_tarski(k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1646,c_1635])).

cnf(c_7,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1652,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3859,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2708,c_1652])).

cnf(c_1887,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1907,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_463])).

cnf(c_1993,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2108,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),u1_struct_0(sK1))
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
    inference(instantiation,[status(thm)],[c_1993])).

cnf(c_5208,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3859,c_24,c_1887,c_1907,c_2108])).

cnf(c_9564,plain,
    ( sK3 != sK3
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9553,c_5208])).

cnf(c_9565,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_9564])).

cnf(c_45,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9565,c_45,c_44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:44:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.61/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/0.97  
% 3.61/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.61/0.97  
% 3.61/0.97  ------  iProver source info
% 3.61/0.97  
% 3.61/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.61/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.61/0.97  git: non_committed_changes: false
% 3.61/0.97  git: last_make_outside_of_git: false
% 3.61/0.97  
% 3.61/0.97  ------ 
% 3.61/0.97  ------ Parsing...
% 3.61/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.61/0.97  
% 3.61/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.61/0.97  
% 3.61/0.97  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.61/0.97  
% 3.61/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/0.97  ------ Proving...
% 3.61/0.97  ------ Problem Properties 
% 3.61/0.97  
% 3.61/0.97  
% 3.61/0.97  clauses                                 27
% 3.61/0.97  conjectures                             11
% 3.61/0.97  EPR                                     12
% 3.61/0.97  Horn                                    26
% 3.61/0.97  unary                                   12
% 3.61/0.97  binary                                  6
% 3.61/0.97  lits                                    62
% 3.61/0.97  lits eq                                 7
% 3.61/0.97  fd_pure                                 0
% 3.61/0.97  fd_pseudo                               0
% 3.61/0.97  fd_cond                                 0
% 3.61/0.97  fd_pseudo_cond                          1
% 3.61/0.97  AC symbols                              0
% 3.61/0.97  
% 3.61/0.97  ------ Input Options Time Limit: Unbounded
% 3.61/0.97  
% 3.61/0.97  
% 3.61/0.97  ------ 
% 3.61/0.97  Current options:
% 3.61/0.97  ------ 
% 3.61/0.97  
% 3.61/0.97  
% 3.61/0.97  
% 3.61/0.97  
% 3.61/0.97  ------ Proving...
% 3.61/0.97  
% 3.61/0.97  
% 3.61/0.97  % SZS status Theorem for theBenchmark.p
% 3.61/0.97  
% 3.61/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.61/0.97  
% 3.61/0.97  fof(f17,conjecture,(
% 3.61/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 3.61/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.97  
% 3.61/0.97  fof(f18,negated_conjecture,(
% 3.61/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 3.61/0.97    inference(negated_conjecture,[],[f17])).
% 3.61/0.97  
% 3.61/0.97  fof(f39,plain,(
% 3.61/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.61/0.97    inference(ennf_transformation,[],[f18])).
% 3.61/0.97  
% 3.61/0.97  fof(f40,plain,(
% 3.61/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.61/0.97    inference(flattening,[],[f39])).
% 3.61/0.97  
% 3.61/0.97  fof(f50,plain,(
% 3.61/0.97    ( ! [X2,X0,X1] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 3.61/0.97    introduced(choice_axiom,[])).
% 3.61/0.97  
% 3.61/0.97  fof(f49,plain,(
% 3.61/0.97    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 3.61/0.97    introduced(choice_axiom,[])).
% 3.61/0.97  
% 3.61/0.97  fof(f48,plain,(
% 3.61/0.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.61/0.97    introduced(choice_axiom,[])).
% 3.61/0.97  
% 3.61/0.97  fof(f47,plain,(
% 3.61/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.61/0.97    introduced(choice_axiom,[])).
% 3.61/0.97  
% 3.61/0.97  fof(f51,plain,(
% 3.61/0.97    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.61/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f50,f49,f48,f47])).
% 3.61/0.97  
% 3.61/0.97  fof(f81,plain,(
% 3.61/0.97    m1_pre_topc(sK2,sK1)),
% 3.61/0.97    inference(cnf_transformation,[],[f51])).
% 3.61/0.97  
% 3.61/0.97  fof(f15,axiom,(
% 3.61/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.61/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.97  
% 3.61/0.97  fof(f37,plain,(
% 3.61/0.97    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.61/0.97    inference(ennf_transformation,[],[f15])).
% 3.61/0.97  
% 3.61/0.97  fof(f72,plain,(
% 3.61/0.97    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.61/0.97    inference(cnf_transformation,[],[f37])).
% 3.61/0.97  
% 3.61/0.97  fof(f2,axiom,(
% 3.61/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.61/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.97  
% 3.61/0.97  fof(f43,plain,(
% 3.61/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.61/0.97    inference(nnf_transformation,[],[f2])).
% 3.61/0.97  
% 3.61/0.97  fof(f55,plain,(
% 3.61/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.61/0.97    inference(cnf_transformation,[],[f43])).
% 3.61/0.97  
% 3.61/0.97  fof(f1,axiom,(
% 3.61/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.61/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.97  
% 3.61/0.97  fof(f41,plain,(
% 3.61/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.61/0.97    inference(nnf_transformation,[],[f1])).
% 3.61/0.97  
% 3.61/0.97  fof(f42,plain,(
% 3.61/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.61/0.97    inference(flattening,[],[f41])).
% 3.61/0.97  
% 3.61/0.97  fof(f54,plain,(
% 3.61/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.61/0.97    inference(cnf_transformation,[],[f42])).
% 3.61/0.97  
% 3.61/0.97  fof(f9,axiom,(
% 3.61/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.61/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.97  
% 3.61/0.97  fof(f28,plain,(
% 3.61/0.97    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.61/0.97    inference(ennf_transformation,[],[f9])).
% 3.61/0.97  
% 3.61/0.97  fof(f64,plain,(
% 3.61/0.97    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.61/0.97    inference(cnf_transformation,[],[f28])).
% 3.61/0.97  
% 3.61/0.97  fof(f79,plain,(
% 3.61/0.97    l1_pre_topc(sK1)),
% 3.61/0.97    inference(cnf_transformation,[],[f51])).
% 3.61/0.97  
% 3.61/0.97  fof(f16,axiom,(
% 3.61/0.97    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.61/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.97  
% 3.61/0.97  fof(f38,plain,(
% 3.61/0.97    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.61/0.97    inference(ennf_transformation,[],[f16])).
% 3.61/0.97  
% 3.61/0.97  fof(f73,plain,(
% 3.61/0.97    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.61/0.97    inference(cnf_transformation,[],[f38])).
% 3.61/0.97  
% 3.61/0.97  fof(f12,axiom,(
% 3.61/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.61/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.97  
% 3.61/0.97  fof(f32,plain,(
% 3.61/0.97    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.61/0.97    inference(ennf_transformation,[],[f12])).
% 3.61/0.97  
% 3.61/0.97  fof(f45,plain,(
% 3.61/0.97    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.61/0.97    inference(nnf_transformation,[],[f32])).
% 3.61/0.97  
% 3.61/0.97  fof(f67,plain,(
% 3.61/0.97    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.61/0.97    inference(cnf_transformation,[],[f45])).
% 3.61/0.97  
% 3.61/0.97  fof(f85,plain,(
% 3.61/0.97    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 3.61/0.97    inference(cnf_transformation,[],[f51])).
% 3.61/0.97  
% 3.61/0.97  fof(f11,axiom,(
% 3.61/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.61/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.97  
% 3.61/0.97  fof(f31,plain,(
% 3.61/0.97    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.61/0.97    inference(ennf_transformation,[],[f11])).
% 3.61/0.97  
% 3.61/0.97  fof(f66,plain,(
% 3.61/0.97    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.61/0.97    inference(cnf_transformation,[],[f31])).
% 3.61/0.97  
% 3.61/0.97  fof(f84,plain,(
% 3.61/0.97    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 3.61/0.97    inference(cnf_transformation,[],[f51])).
% 3.61/0.97  
% 3.61/0.97  fof(f14,axiom,(
% 3.61/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 3.61/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.97  
% 3.61/0.97  fof(f35,plain,(
% 3.61/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.61/0.97    inference(ennf_transformation,[],[f14])).
% 3.61/0.97  
% 3.61/0.97  fof(f36,plain,(
% 3.61/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.61/0.97    inference(flattening,[],[f35])).
% 3.61/0.97  
% 3.61/0.97  fof(f71,plain,(
% 3.61/0.97    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.61/0.97    inference(cnf_transformation,[],[f36])).
% 3.61/0.97  
% 3.61/0.97  fof(f82,plain,(
% 3.61/0.97    v1_funct_1(sK3)),
% 3.61/0.97    inference(cnf_transformation,[],[f51])).
% 3.61/0.97  
% 3.61/0.97  fof(f7,axiom,(
% 3.61/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.61/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.97  
% 3.61/0.97  fof(f25,plain,(
% 3.61/0.97    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.61/0.97    inference(ennf_transformation,[],[f7])).
% 3.61/0.97  
% 3.61/0.97  fof(f26,plain,(
% 3.61/0.97    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.61/0.97    inference(flattening,[],[f25])).
% 3.61/0.97  
% 3.61/0.97  fof(f62,plain,(
% 3.61/0.97    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.61/0.97    inference(cnf_transformation,[],[f26])).
% 3.61/0.97  
% 3.61/0.97  fof(f74,plain,(
% 3.61/0.97    ~v2_struct_0(sK0)),
% 3.61/0.97    inference(cnf_transformation,[],[f51])).
% 3.61/0.97  
% 3.61/0.97  fof(f75,plain,(
% 3.61/0.97    v2_pre_topc(sK0)),
% 3.61/0.97    inference(cnf_transformation,[],[f51])).
% 3.61/0.97  
% 3.61/0.97  fof(f76,plain,(
% 3.61/0.97    l1_pre_topc(sK0)),
% 3.61/0.97    inference(cnf_transformation,[],[f51])).
% 3.61/0.97  
% 3.61/0.97  fof(f77,plain,(
% 3.61/0.97    ~v2_struct_0(sK1)),
% 3.61/0.97    inference(cnf_transformation,[],[f51])).
% 3.61/0.97  
% 3.61/0.97  fof(f78,plain,(
% 3.61/0.97    v2_pre_topc(sK1)),
% 3.61/0.97    inference(cnf_transformation,[],[f51])).
% 3.61/0.97  
% 3.61/0.97  fof(f83,plain,(
% 3.61/0.97    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 3.61/0.97    inference(cnf_transformation,[],[f51])).
% 3.61/0.97  
% 3.61/0.97  fof(f8,axiom,(
% 3.61/0.97    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.61/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.97  
% 3.61/0.97  fof(f27,plain,(
% 3.61/0.97    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.61/0.97    inference(ennf_transformation,[],[f8])).
% 3.61/0.97  
% 3.61/0.97  fof(f63,plain,(
% 3.61/0.97    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.61/0.97    inference(cnf_transformation,[],[f27])).
% 3.61/0.97  
% 3.61/0.97  fof(f10,axiom,(
% 3.61/0.97    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.61/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.97  
% 3.61/0.97  fof(f29,plain,(
% 3.61/0.97    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.61/0.97    inference(ennf_transformation,[],[f10])).
% 3.61/0.97  
% 3.61/0.97  fof(f30,plain,(
% 3.61/0.97    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.61/0.97    inference(flattening,[],[f29])).
% 3.61/0.97  
% 3.61/0.97  fof(f65,plain,(
% 3.61/0.97    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.61/0.97    inference(cnf_transformation,[],[f30])).
% 3.61/0.97  
% 3.61/0.97  fof(f13,axiom,(
% 3.61/0.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.61/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.97  
% 3.61/0.97  fof(f33,plain,(
% 3.61/0.97    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.61/0.97    inference(ennf_transformation,[],[f13])).
% 3.61/0.97  
% 3.61/0.97  fof(f34,plain,(
% 3.61/0.97    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.61/0.97    inference(flattening,[],[f33])).
% 3.61/0.97  
% 3.61/0.97  fof(f46,plain,(
% 3.61/0.97    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.61/0.97    inference(nnf_transformation,[],[f34])).
% 3.61/0.97  
% 3.61/0.97  fof(f70,plain,(
% 3.61/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.61/0.97    inference(cnf_transformation,[],[f46])).
% 3.61/0.97  
% 3.61/0.97  fof(f89,plain,(
% 3.61/0.97    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.61/0.97    inference(equality_resolution,[],[f70])).
% 3.61/0.97  
% 3.61/0.97  fof(f86,plain,(
% 3.61/0.97    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 3.61/0.97    inference(cnf_transformation,[],[f51])).
% 3.61/0.97  
% 3.61/0.97  fof(f6,axiom,(
% 3.61/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.61/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.97  
% 3.61/0.97  fof(f19,plain,(
% 3.61/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.61/0.97    inference(pure_predicate_removal,[],[f6])).
% 3.61/0.97  
% 3.61/0.97  fof(f24,plain,(
% 3.61/0.97    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.97    inference(ennf_transformation,[],[f19])).
% 3.61/0.97  
% 3.61/0.97  fof(f61,plain,(
% 3.61/0.97    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.97    inference(cnf_transformation,[],[f24])).
% 3.61/0.97  
% 3.61/0.97  fof(f3,axiom,(
% 3.61/0.97    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.61/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.97  
% 3.61/0.97  fof(f20,plain,(
% 3.61/0.97    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.61/0.97    inference(ennf_transformation,[],[f3])).
% 3.61/0.97  
% 3.61/0.97  fof(f44,plain,(
% 3.61/0.97    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.61/0.97    inference(nnf_transformation,[],[f20])).
% 3.61/0.97  
% 3.61/0.97  fof(f57,plain,(
% 3.61/0.97    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.61/0.97    inference(cnf_transformation,[],[f44])).
% 3.61/0.97  
% 3.61/0.97  fof(f5,axiom,(
% 3.61/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.61/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.97  
% 3.61/0.97  fof(f23,plain,(
% 3.61/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.97    inference(ennf_transformation,[],[f5])).
% 3.61/0.97  
% 3.61/0.97  fof(f60,plain,(
% 3.61/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.97    inference(cnf_transformation,[],[f23])).
% 3.61/0.97  
% 3.61/0.97  fof(f4,axiom,(
% 3.61/0.97    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.61/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.97  
% 3.61/0.97  fof(f21,plain,(
% 3.61/0.97    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.61/0.97    inference(ennf_transformation,[],[f4])).
% 3.61/0.97  
% 3.61/0.97  fof(f22,plain,(
% 3.61/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.61/0.97    inference(flattening,[],[f21])).
% 3.61/0.97  
% 3.61/0.97  fof(f59,plain,(
% 3.61/0.97    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.61/0.97    inference(cnf_transformation,[],[f22])).
% 3.61/0.97  
% 3.61/0.97  cnf(c_27,negated_conjecture,
% 3.61/0.97      ( m1_pre_topc(sK2,sK1) ),
% 3.61/0.97      inference(cnf_transformation,[],[f81]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_1644,plain,
% 3.61/0.97      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_20,plain,
% 3.61/0.97      ( ~ m1_pre_topc(X0,X1)
% 3.61/0.97      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.61/0.97      | ~ l1_pre_topc(X1) ),
% 3.61/0.97      inference(cnf_transformation,[],[f72]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_1648,plain,
% 3.61/0.97      ( m1_pre_topc(X0,X1) != iProver_top
% 3.61/0.97      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.61/0.97      | l1_pre_topc(X1) != iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_4,plain,
% 3.61/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.61/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_1653,plain,
% 3.61/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.61/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_3876,plain,
% 3.61/0.97      ( m1_pre_topc(X0,X1) != iProver_top
% 3.61/0.97      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.61/0.97      | l1_pre_topc(X1) != iProver_top ),
% 3.61/0.97      inference(superposition,[status(thm)],[c_1648,c_1653]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_0,plain,
% 3.61/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.61/0.97      inference(cnf_transformation,[],[f54]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_1656,plain,
% 3.61/0.97      ( X0 = X1
% 3.61/0.97      | r1_tarski(X0,X1) != iProver_top
% 3.61/0.97      | r1_tarski(X1,X0) != iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_6015,plain,
% 3.61/0.97      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.61/0.97      | m1_pre_topc(X1,X0) != iProver_top
% 3.61/0.97      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.61/0.97      | l1_pre_topc(X0) != iProver_top ),
% 3.61/0.97      inference(superposition,[status(thm)],[c_3876,c_1656]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_6345,plain,
% 3.61/0.97      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.61/0.97      | m1_pre_topc(X1,X0) != iProver_top
% 3.61/0.97      | m1_pre_topc(X0,X1) != iProver_top
% 3.61/0.97      | l1_pre_topc(X1) != iProver_top
% 3.61/0.97      | l1_pre_topc(X0) != iProver_top ),
% 3.61/0.97      inference(superposition,[status(thm)],[c_3876,c_6015]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_12,plain,
% 3.61/0.97      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.61/0.97      inference(cnf_transformation,[],[f64]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_70,plain,
% 3.61/0.97      ( m1_pre_topc(X0,X1) != iProver_top
% 3.61/0.97      | l1_pre_topc(X1) != iProver_top
% 3.61/0.97      | l1_pre_topc(X0) = iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_3708,plain,
% 3.61/0.97      ( ~ m1_pre_topc(X0,X1)
% 3.61/0.97      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.61/0.97      | ~ l1_pre_topc(X1) ),
% 3.61/0.97      inference(resolution,[status(thm)],[c_20,c_4]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_3709,plain,
% 3.61/0.97      ( m1_pre_topc(X0,X1) != iProver_top
% 3.61/0.97      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.61/0.97      | l1_pre_topc(X1) != iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_3708]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_9219,plain,
% 3.61/0.97      ( l1_pre_topc(X1) != iProver_top
% 3.61/0.97      | m1_pre_topc(X0,X1) != iProver_top
% 3.61/0.97      | m1_pre_topc(X1,X0) != iProver_top
% 3.61/0.97      | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.61/0.97      inference(global_propositional_subsumption,
% 3.61/0.97                [status(thm)],
% 3.61/0.97                [c_6345,c_70,c_3709,c_6015]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_9220,plain,
% 3.61/0.97      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.61/0.97      | m1_pre_topc(X0,X1) != iProver_top
% 3.61/0.97      | m1_pre_topc(X1,X0) != iProver_top
% 3.61/0.97      | l1_pre_topc(X1) != iProver_top ),
% 3.61/0.97      inference(renaming,[status(thm)],[c_9219]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_9229,plain,
% 3.61/0.97      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 3.61/0.97      | m1_pre_topc(sK1,sK2) != iProver_top
% 3.61/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.61/0.97      inference(superposition,[status(thm)],[c_1644,c_9220]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_29,negated_conjecture,
% 3.61/0.97      ( l1_pre_topc(sK1) ),
% 3.61/0.97      inference(cnf_transformation,[],[f79]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_40,plain,
% 3.61/0.97      ( l1_pre_topc(sK1) = iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_21,plain,
% 3.61/0.97      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.61/0.97      inference(cnf_transformation,[],[f73]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_47,plain,
% 3.61/0.97      ( m1_pre_topc(X0,X0) = iProver_top
% 3.61/0.97      | l1_pre_topc(X0) != iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_49,plain,
% 3.61/0.97      ( m1_pre_topc(sK1,sK1) = iProver_top
% 3.61/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.61/0.97      inference(instantiation,[status(thm)],[c_47]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_16,plain,
% 3.61/0.97      ( ~ m1_pre_topc(X0,X1)
% 3.61/0.97      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.61/0.97      | ~ l1_pre_topc(X0)
% 3.61/0.97      | ~ l1_pre_topc(X1) ),
% 3.61/0.97      inference(cnf_transformation,[],[f67]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_62,plain,
% 3.61/0.97      ( m1_pre_topc(X0,X1) != iProver_top
% 3.61/0.97      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.61/0.97      | l1_pre_topc(X0) != iProver_top
% 3.61/0.97      | l1_pre_topc(X1) != iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_64,plain,
% 3.61/0.97      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.61/0.97      | m1_pre_topc(sK1,sK1) != iProver_top
% 3.61/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.61/0.97      inference(instantiation,[status(thm)],[c_62]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_2461,plain,
% 3.61/0.97      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK1) ),
% 3.61/0.97      inference(resolution,[status(thm)],[c_12,c_27]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_2462,plain,
% 3.61/0.97      ( l1_pre_topc(sK2) = iProver_top
% 3.61/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_2461]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_23,negated_conjecture,
% 3.61/0.97      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.61/0.97      inference(cnf_transformation,[],[f85]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_14,plain,
% 3.61/0.97      ( m1_pre_topc(X0,X1)
% 3.61/0.97      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.61/0.97      | ~ l1_pre_topc(X1) ),
% 3.61/0.97      inference(cnf_transformation,[],[f66]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_1649,plain,
% 3.61/0.97      ( m1_pre_topc(X0,X1) = iProver_top
% 3.61/0.97      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.61/0.97      | l1_pre_topc(X1) != iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_4005,plain,
% 3.61/0.97      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.61/0.97      | m1_pre_topc(X0,sK2) = iProver_top
% 3.61/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.61/0.97      inference(superposition,[status(thm)],[c_23,c_1649]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_4020,plain,
% 3.61/0.97      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.61/0.97      | m1_pre_topc(sK1,sK2) = iProver_top
% 3.61/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.61/0.97      inference(instantiation,[status(thm)],[c_4005]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_9550,plain,
% 3.61/0.97      ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 3.61/0.97      inference(global_propositional_subsumption,
% 3.61/0.97                [status(thm)],
% 3.61/0.97                [c_9229,c_40,c_49,c_64,c_2462,c_4020]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_24,negated_conjecture,
% 3.61/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 3.61/0.97      inference(cnf_transformation,[],[f84]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_1646,plain,
% 3.61/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_19,plain,
% 3.61/0.97      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.61/0.97      | ~ m1_pre_topc(X3,X1)
% 3.61/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.61/0.97      | ~ v2_pre_topc(X2)
% 3.61/0.97      | ~ v2_pre_topc(X1)
% 3.61/0.97      | v2_struct_0(X1)
% 3.61/0.97      | v2_struct_0(X2)
% 3.61/0.97      | ~ l1_pre_topc(X1)
% 3.61/0.97      | ~ l1_pre_topc(X2)
% 3.61/0.97      | ~ v1_funct_1(X0)
% 3.61/0.97      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.61/0.97      inference(cnf_transformation,[],[f71]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_26,negated_conjecture,
% 3.61/0.97      ( v1_funct_1(sK3) ),
% 3.61/0.97      inference(cnf_transformation,[],[f82]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_573,plain,
% 3.61/0.97      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.61/0.97      | ~ m1_pre_topc(X3,X1)
% 3.61/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.61/0.97      | ~ v2_pre_topc(X1)
% 3.61/0.97      | ~ v2_pre_topc(X2)
% 3.61/0.97      | v2_struct_0(X1)
% 3.61/0.97      | v2_struct_0(X2)
% 3.61/0.97      | ~ l1_pre_topc(X1)
% 3.61/0.97      | ~ l1_pre_topc(X2)
% 3.61/0.97      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 3.61/0.97      | sK3 != X0 ),
% 3.61/0.97      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_574,plain,
% 3.61/0.97      ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
% 3.61/0.97      | ~ m1_pre_topc(X2,X0)
% 3.61/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.61/0.97      | ~ v2_pre_topc(X0)
% 3.61/0.97      | ~ v2_pre_topc(X1)
% 3.61/0.97      | v2_struct_0(X0)
% 3.61/0.97      | v2_struct_0(X1)
% 3.61/0.97      | ~ l1_pre_topc(X0)
% 3.61/0.97      | ~ l1_pre_topc(X1)
% 3.61/0.97      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2) ),
% 3.61/0.97      inference(unflattening,[status(thm)],[c_573]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_1634,plain,
% 3.61/0.97      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2)
% 3.61/0.97      | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.61/0.97      | m1_pre_topc(X2,X0) != iProver_top
% 3.61/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.61/0.97      | v2_pre_topc(X1) != iProver_top
% 3.61/0.97      | v2_pre_topc(X0) != iProver_top
% 3.61/0.97      | v2_struct_0(X1) = iProver_top
% 3.61/0.97      | v2_struct_0(X0) = iProver_top
% 3.61/0.97      | l1_pre_topc(X0) != iProver_top
% 3.61/0.97      | l1_pre_topc(X1) != iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_574]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_2422,plain,
% 3.61/0.97      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 3.61/0.97      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.61/0.97      | m1_pre_topc(X0,sK1) != iProver_top
% 3.61/0.97      | v2_pre_topc(sK0) != iProver_top
% 3.61/0.97      | v2_pre_topc(sK1) != iProver_top
% 3.61/0.97      | v2_struct_0(sK0) = iProver_top
% 3.61/0.97      | v2_struct_0(sK1) = iProver_top
% 3.61/0.97      | l1_pre_topc(sK0) != iProver_top
% 3.61/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.61/0.97      inference(superposition,[status(thm)],[c_1646,c_1634]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_10,plain,
% 3.61/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.97      | ~ v1_funct_1(X0)
% 3.61/0.97      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.61/0.97      inference(cnf_transformation,[],[f62]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_609,plain,
% 3.61/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.97      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 3.61/0.97      | sK3 != X0 ),
% 3.61/0.97      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_610,plain,
% 3.61/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.61/0.97      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.61/0.97      inference(unflattening,[status(thm)],[c_609]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_1633,plain,
% 3.61/0.97      ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 3.61/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_610]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_2243,plain,
% 3.61/0.97      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.61/0.97      inference(superposition,[status(thm)],[c_1646,c_1633]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_2423,plain,
% 3.61/0.97      ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
% 3.61/0.97      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.61/0.97      | m1_pre_topc(X0,sK1) != iProver_top
% 3.61/0.97      | v2_pre_topc(sK0) != iProver_top
% 3.61/0.97      | v2_pre_topc(sK1) != iProver_top
% 3.61/0.97      | v2_struct_0(sK0) = iProver_top
% 3.61/0.97      | v2_struct_0(sK1) = iProver_top
% 3.61/0.97      | l1_pre_topc(sK0) != iProver_top
% 3.61/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.61/0.97      inference(demodulation,[status(thm)],[c_2422,c_2243]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_34,negated_conjecture,
% 3.61/0.97      ( ~ v2_struct_0(sK0) ),
% 3.61/0.97      inference(cnf_transformation,[],[f74]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_35,plain,
% 3.61/0.97      ( v2_struct_0(sK0) != iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_33,negated_conjecture,
% 3.61/0.97      ( v2_pre_topc(sK0) ),
% 3.61/0.97      inference(cnf_transformation,[],[f75]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_36,plain,
% 3.61/0.97      ( v2_pre_topc(sK0) = iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_32,negated_conjecture,
% 3.61/0.97      ( l1_pre_topc(sK0) ),
% 3.61/0.97      inference(cnf_transformation,[],[f76]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_37,plain,
% 3.61/0.97      ( l1_pre_topc(sK0) = iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_31,negated_conjecture,
% 3.61/0.97      ( ~ v2_struct_0(sK1) ),
% 3.61/0.97      inference(cnf_transformation,[],[f77]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_38,plain,
% 3.61/0.97      ( v2_struct_0(sK1) != iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_30,negated_conjecture,
% 3.61/0.97      ( v2_pre_topc(sK1) ),
% 3.61/0.97      inference(cnf_transformation,[],[f78]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_39,plain,
% 3.61/0.97      ( v2_pre_topc(sK1) = iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_25,negated_conjecture,
% 3.61/0.97      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 3.61/0.97      inference(cnf_transformation,[],[f83]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_44,plain,
% 3.61/0.97      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_2428,plain,
% 3.61/0.97      ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
% 3.61/0.97      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.61/0.97      inference(global_propositional_subsumption,
% 3.61/0.97                [status(thm)],
% 3.61/0.97                [c_2423,c_35,c_36,c_37,c_38,c_39,c_40,c_44]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_2436,plain,
% 3.61/0.97      ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 3.61/0.97      inference(superposition,[status(thm)],[c_1644,c_2428]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_11,plain,
% 3.61/0.97      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.61/0.97      inference(cnf_transformation,[],[f63]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_13,plain,
% 3.61/0.97      ( v2_struct_0(X0)
% 3.61/0.97      | ~ v1_xboole_0(u1_struct_0(X0))
% 3.61/0.97      | ~ l1_struct_0(X0) ),
% 3.61/0.97      inference(cnf_transformation,[],[f65]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_440,plain,
% 3.61/0.97      ( v2_struct_0(X0)
% 3.61/0.97      | ~ v1_xboole_0(u1_struct_0(X0))
% 3.61/0.97      | ~ l1_pre_topc(X0) ),
% 3.61/0.97      inference(resolution,[status(thm)],[c_11,c_13]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_17,plain,
% 3.61/0.97      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 3.61/0.97      | ~ v1_funct_2(X4,X2,X3)
% 3.61/0.97      | ~ v1_funct_2(X4,X0,X1)
% 3.61/0.97      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.61/0.97      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.61/0.97      | v1_xboole_0(X1)
% 3.61/0.97      | v1_xboole_0(X3)
% 3.61/0.97      | ~ v1_funct_1(X4) ),
% 3.61/0.97      inference(cnf_transformation,[],[f89]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_22,negated_conjecture,
% 3.61/0.97      ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
% 3.61/0.97      inference(cnf_transformation,[],[f86]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_498,plain,
% 3.61/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 3.61/0.97      | ~ v1_funct_2(X0,X3,X4)
% 3.61/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.61/0.97      | v1_xboole_0(X4)
% 3.61/0.97      | v1_xboole_0(X2)
% 3.61/0.97      | ~ v1_funct_1(X0)
% 3.61/0.97      | k2_tmap_1(sK1,sK0,sK3,sK2) != X0
% 3.61/0.97      | u1_struct_0(sK2) != X1
% 3.61/0.97      | u1_struct_0(sK0) != X2
% 3.61/0.97      | u1_struct_0(sK0) != X4
% 3.61/0.97      | u1_struct_0(sK1) != X3
% 3.61/0.97      | sK3 != X0 ),
% 3.61/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_499,plain,
% 3.61/0.97      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 3.61/0.97      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.61/0.97      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 3.61/0.97      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.61/0.97      | v1_xboole_0(u1_struct_0(sK0))
% 3.61/0.97      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 3.61/0.97      | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 3.61/0.97      inference(unflattening,[status(thm)],[c_498]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_531,plain,
% 3.61/0.97      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 3.61/0.97      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.61/0.97      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 3.61/0.97      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.61/0.97      | v2_struct_0(X0)
% 3.61/0.97      | ~ l1_pre_topc(X0)
% 3.61/0.97      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 3.61/0.97      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 3.61/0.97      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 3.61/0.97      inference(resolution_lifted,[status(thm)],[c_440,c_499]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_621,plain,
% 3.61/0.97      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 3.61/0.97      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.61/0.97      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 3.61/0.97      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.61/0.97      | v2_struct_0(X0)
% 3.61/0.97      | ~ l1_pre_topc(X0)
% 3.61/0.97      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 3.61/0.97      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 3.61/0.97      inference(resolution_lifted,[status(thm)],[c_26,c_531]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_918,plain,
% 3.61/0.97      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 3.61/0.97      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.61/0.97      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 3.61/0.97      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.61/0.97      | sP0_iProver_split
% 3.61/0.97      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
% 3.61/0.97      inference(splitting,
% 3.61/0.97                [splitting(split),new_symbols(definition,[])],
% 3.61/0.97                [c_621]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_1631,plain,
% 3.61/0.97      ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 3.61/0.97      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.61/0.97      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.61/0.97      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.61/0.97      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.61/0.97      | sP0_iProver_split = iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_918]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_2561,plain,
% 3.61/0.97      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 3.61/0.97      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.61/0.97      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.61/0.97      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.61/0.97      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.61/0.97      | sP0_iProver_split = iProver_top ),
% 3.61/0.97      inference(demodulation,[status(thm)],[c_2436,c_1631]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_917,plain,
% 3.61/0.97      ( v2_struct_0(X0)
% 3.61/0.97      | ~ l1_pre_topc(X0)
% 3.61/0.97      | u1_struct_0(X0) != u1_struct_0(sK0)
% 3.61/0.97      | ~ sP0_iProver_split ),
% 3.61/0.97      inference(splitting,
% 3.61/0.97                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.61/0.97                [c_621]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_920,plain,( X0 = X0 ),theory(equality) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_2254,plain,
% 3.61/0.97      ( v2_struct_0(sK0) | ~ l1_pre_topc(sK0) | ~ sP0_iProver_split ),
% 3.61/0.97      inference(resolution,[status(thm)],[c_917,c_920]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_2255,plain,
% 3.61/0.97      ( v2_struct_0(sK0) = iProver_top
% 3.61/0.97      | l1_pre_topc(sK0) != iProver_top
% 3.61/0.97      | sP0_iProver_split != iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_2254]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_2564,plain,
% 3.61/0.97      ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.61/0.97      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.61/0.97      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.61/0.97      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.61/0.97      | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
% 3.61/0.97      inference(global_propositional_subsumption,
% 3.61/0.97                [status(thm)],
% 3.61/0.97                [c_2561,c_35,c_37,c_2255]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_2565,plain,
% 3.61/0.97      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 3.61/0.97      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.61/0.97      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.61/0.97      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.61/0.97      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 3.61/0.97      inference(renaming,[status(thm)],[c_2564]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_9553,plain,
% 3.61/0.97      ( k7_relat_1(sK3,u1_struct_0(sK1)) != sK3
% 3.61/0.97      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.61/0.97      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 3.61/0.97      inference(demodulation,[status(thm)],[c_9550,c_2565]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_9,plain,
% 3.61/0.97      ( v4_relat_1(X0,X1)
% 3.61/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.61/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_6,plain,
% 3.61/0.97      ( ~ v4_relat_1(X0,X1)
% 3.61/0.97      | r1_tarski(k1_relat_1(X0),X1)
% 3.61/0.97      | ~ v1_relat_1(X0) ),
% 3.61/0.97      inference(cnf_transformation,[],[f57]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_458,plain,
% 3.61/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.97      | r1_tarski(k1_relat_1(X0),X1)
% 3.61/0.97      | ~ v1_relat_1(X0) ),
% 3.61/0.97      inference(resolution,[status(thm)],[c_9,c_6]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_8,plain,
% 3.61/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.97      | v1_relat_1(X0) ),
% 3.61/0.97      inference(cnf_transformation,[],[f60]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_462,plain,
% 3.61/0.97      ( r1_tarski(k1_relat_1(X0),X1)
% 3.61/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.61/0.97      inference(global_propositional_subsumption,
% 3.61/0.97                [status(thm)],
% 3.61/0.97                [c_458,c_8]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_463,plain,
% 3.61/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.97      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.61/0.97      inference(renaming,[status(thm)],[c_462]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_1635,plain,
% 3.61/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.61/0.97      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_2708,plain,
% 3.61/0.97      ( r1_tarski(k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
% 3.61/0.97      inference(superposition,[status(thm)],[c_1646,c_1635]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_7,plain,
% 3.61/0.97      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.61/0.97      | ~ v1_relat_1(X0)
% 3.61/0.97      | k7_relat_1(X0,X1) = X0 ),
% 3.61/0.97      inference(cnf_transformation,[],[f59]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_1652,plain,
% 3.61/0.97      ( k7_relat_1(X0,X1) = X0
% 3.61/0.97      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.61/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_3859,plain,
% 3.61/0.97      ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3
% 3.61/0.97      | v1_relat_1(sK3) != iProver_top ),
% 3.61/0.97      inference(superposition,[status(thm)],[c_2708,c_1652]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_1887,plain,
% 3.61/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.61/0.97      | v1_relat_1(sK3) ),
% 3.61/0.97      inference(instantiation,[status(thm)],[c_8]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_1907,plain,
% 3.61/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.61/0.97      | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK1)) ),
% 3.61/0.97      inference(instantiation,[status(thm)],[c_463]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_1993,plain,
% 3.61/0.97      ( ~ r1_tarski(k1_relat_1(sK3),X0)
% 3.61/0.97      | ~ v1_relat_1(sK3)
% 3.61/0.97      | k7_relat_1(sK3,X0) = sK3 ),
% 3.61/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_2108,plain,
% 3.61/0.97      ( ~ r1_tarski(k1_relat_1(sK3),u1_struct_0(sK1))
% 3.61/0.97      | ~ v1_relat_1(sK3)
% 3.61/0.97      | k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
% 3.61/0.97      inference(instantiation,[status(thm)],[c_1993]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_5208,plain,
% 3.61/0.97      ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
% 3.61/0.97      inference(global_propositional_subsumption,
% 3.61/0.97                [status(thm)],
% 3.61/0.97                [c_3859,c_24,c_1887,c_1907,c_2108]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_9564,plain,
% 3.61/0.97      ( sK3 != sK3
% 3.61/0.97      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.61/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 3.61/0.97      inference(light_normalisation,[status(thm)],[c_9553,c_5208]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_9565,plain,
% 3.61/0.97      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.61/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 3.61/0.97      inference(equality_resolution_simp,[status(thm)],[c_9564]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(c_45,plain,
% 3.61/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 3.61/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.61/0.97  
% 3.61/0.97  cnf(contradiction,plain,
% 3.61/0.97      ( $false ),
% 3.61/0.97      inference(minisat,[status(thm)],[c_9565,c_45,c_44]) ).
% 3.61/0.97  
% 3.61/0.97  
% 3.61/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.61/0.97  
% 3.61/0.97  ------                               Statistics
% 3.61/0.97  
% 3.61/0.97  ------ Selected
% 3.61/0.97  
% 3.61/0.97  total_time:                             0.313
% 3.61/0.97  
%------------------------------------------------------------------------------
