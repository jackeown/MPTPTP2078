%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:26 EST 2020

% Result     : Theorem 0.36s
% Output     : CNFRefutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  233 (1637 expanded)
%              Number of clauses        :  140 ( 492 expanded)
%              Number of leaves         :   23 ( 495 expanded)
%              Depth                    :   26
%              Number of atoms          :  933 (13471 expanded)
%              Number of equality atoms :  338 (1826 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f49,plain,(
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
    inference(flattening,[],[f49])).

fof(f60,plain,(
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

fof(f59,plain,(
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

fof(f58,plain,(
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

fof(f57,plain,
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

fof(f61,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f50,f60,f59,f58,f57])).

fof(f93,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f71,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f97,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f61])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f83,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
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
    inference(flattening,[],[f47])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f90,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f74,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f69,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f16])).

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
    inference(flattening,[],[f44])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f103,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f96,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f61])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f80,plain,(
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

fof(f94,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f87,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f88,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f89,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f95,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f61])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f73,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f54,plain,(
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

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f101,plain,(
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
    inference(equality_resolution,[],[f79])).

fof(f98,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f61])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1346,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_214,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_9])).

cnf(c_215,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_214])).

cnf(c_1336,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_25,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_13,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1352,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2863,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1352])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_42,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1355,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2326,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1346,c_1355])).

cnf(c_3006,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2863,c_42,c_2326])).

cnf(c_3007,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_3006])).

cnf(c_3014,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1336,c_3007])).

cnf(c_3121,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3014,c_42])).

cnf(c_3122,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3121])).

cnf(c_3130,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1346,c_3122])).

cnf(c_21,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1351,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3129,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1351,c_3122])).

cnf(c_53,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_55,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_70,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_72,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_2880,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2863])).

cnf(c_3402,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3129,c_42,c_55,c_72,c_2326,c_2880])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1350,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3720,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3402,c_1350])).

cnf(c_6368,plain,
    ( v2_pre_topc(sK2) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3720,c_42,c_2326])).

cnf(c_6369,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6368])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1358,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6376,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK1)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6369,c_1358])).

cnf(c_2718,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1336])).

cnf(c_2981,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2718,c_42,c_2326])).

cnf(c_2982,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2981])).

cnf(c_2990,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2982,c_1352])).

cnf(c_3111,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2990,c_42])).

cnf(c_3112,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_3111])).

cnf(c_3719,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2982,c_1350])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_41,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_12,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_75,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_77,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_10,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_81,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_83,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_81])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1596,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1597,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1596])).

cnf(c_1599,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1597])).

cnf(c_4467,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3719,c_41,c_42,c_77,c_83,c_1599])).

cnf(c_4478,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2982,c_4467])).

cnf(c_3015,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1351,c_3007])).

cnf(c_3216,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3015,c_42,c_83,c_1599])).

cnf(c_20,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_198,plain,
    ( ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_12])).

cnf(c_199,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(renaming,[status(thm)],[c_198])).

cnf(c_1338,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_199])).

cnf(c_1481,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1338,c_1355])).

cnf(c_4649,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2982,c_1481])).

cnf(c_5508,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4649,c_42,c_83,c_1599])).

cnf(c_5509,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5508])).

cnf(c_5520,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3216,c_5509])).

cnf(c_7620,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5520,c_42,c_55,c_72])).

cnf(c_7635,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7620,c_4467])).

cnf(c_4647,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1351,c_1481])).

cnf(c_1354,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1356,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2317,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1354,c_1356])).

cnf(c_6098,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4647,c_2317])).

cnf(c_6099,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6098])).

cnf(c_6120,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6099,c_4467])).

cnf(c_7668,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7635,c_41,c_42,c_3014,c_6120])).

cnf(c_7674,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK1)
    | m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7668,c_1358])).

cnf(c_8073,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK1)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4478,c_7674])).

cnf(c_8109,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK1)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6376,c_42,c_55,c_72,c_2326,c_2880,c_2990,c_8073])).

cnf(c_8121,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_pre_topc(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3130,c_8109])).

cnf(c_8315,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8121,c_42,c_55,c_72,c_2326,c_2880])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1348,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

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
    inference(cnf_transformation,[],[f80])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_514,plain,
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
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_515,plain,
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
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_1334,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_2004,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_1334])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_550,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_28])).

cnf(c_551,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_550])).

cnf(c_1333,plain,
    ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_551])).

cnf(c_1826,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1348,c_1333])).

cnf(c_2005,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2004,c_1826])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_37,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_38,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_39,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_40,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_46,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2072,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2005,c_37,c_38,c_39,c_40,c_41,c_42,c_46])).

cnf(c_2080,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_1346,c_2072])).

cnf(c_8,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_419,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_8,c_11])).

cnf(c_16,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_24,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_439,plain,
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
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_440,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_472,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_419,c_440])).

cnf(c_562,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_28,c_472])).

cnf(c_800,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | sP0_iProver_split
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_562])).

cnf(c_1331,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_800])).

cnf(c_2082,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2080,c_1331])).

cnf(c_799,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_562])).

cnf(c_1332,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK0)
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_1911,plain,
    ( v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1332])).

cnf(c_2161,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2082,c_37,c_39,c_1911])).

cnf(c_2162,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2161])).

cnf(c_8324,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8315,c_2162])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_399,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_5,c_3])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_399,c_5,c_4,c_3])).

cnf(c_1335,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_2173,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
    inference(superposition,[status(thm)],[c_1348,c_1335])).

cnf(c_8335,plain,
    ( sK3 != sK3
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8324,c_2173])).

cnf(c_8336,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8335])).

cnf(c_47,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8336,c_47,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:39:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 0.36/1.06  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.36/1.06  
% 0.36/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.36/1.06  
% 0.36/1.06  ------  iProver source info
% 0.36/1.06  
% 0.36/1.06  git: date: 2020-06-30 10:37:57 +0100
% 0.36/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.36/1.06  git: non_committed_changes: false
% 0.36/1.06  git: last_make_outside_of_git: false
% 0.36/1.06  
% 0.36/1.06  ------ 
% 0.36/1.06  
% 0.36/1.06  ------ Input Options
% 0.36/1.06  
% 0.36/1.06  --out_options                           all
% 0.36/1.06  --tptp_safe_out                         true
% 0.36/1.06  --problem_path                          ""
% 0.36/1.06  --include_path                          ""
% 0.36/1.06  --clausifier                            res/vclausify_rel
% 0.36/1.06  --clausifier_options                    --mode clausify
% 0.36/1.06  --stdin                                 false
% 0.36/1.06  --stats_out                             all
% 0.36/1.06  
% 0.36/1.06  ------ General Options
% 0.36/1.06  
% 0.36/1.06  --fof                                   false
% 0.36/1.06  --time_out_real                         305.
% 0.36/1.06  --time_out_virtual                      -1.
% 0.36/1.06  --symbol_type_check                     false
% 0.36/1.06  --clausify_out                          false
% 0.36/1.06  --sig_cnt_out                           false
% 0.36/1.06  --trig_cnt_out                          false
% 0.36/1.06  --trig_cnt_out_tolerance                1.
% 0.36/1.06  --trig_cnt_out_sk_spl                   false
% 0.36/1.06  --abstr_cl_out                          false
% 0.36/1.06  
% 0.36/1.06  ------ Global Options
% 0.36/1.06  
% 0.36/1.06  --schedule                              default
% 0.36/1.06  --add_important_lit                     false
% 0.36/1.06  --prop_solver_per_cl                    1000
% 0.36/1.06  --min_unsat_core                        false
% 0.36/1.06  --soft_assumptions                      false
% 0.36/1.06  --soft_lemma_size                       3
% 0.36/1.06  --prop_impl_unit_size                   0
% 0.36/1.06  --prop_impl_unit                        []
% 0.36/1.06  --share_sel_clauses                     true
% 0.36/1.06  --reset_solvers                         false
% 0.36/1.06  --bc_imp_inh                            [conj_cone]
% 0.36/1.06  --conj_cone_tolerance                   3.
% 0.36/1.06  --extra_neg_conj                        none
% 0.36/1.06  --large_theory_mode                     true
% 0.36/1.06  --prolific_symb_bound                   200
% 0.36/1.06  --lt_threshold                          2000
% 0.36/1.06  --clause_weak_htbl                      true
% 0.36/1.06  --gc_record_bc_elim                     false
% 0.36/1.06  
% 0.36/1.06  ------ Preprocessing Options
% 0.36/1.06  
% 0.36/1.06  --preprocessing_flag                    true
% 0.36/1.06  --time_out_prep_mult                    0.1
% 0.36/1.06  --splitting_mode                        input
% 0.36/1.06  --splitting_grd                         true
% 0.36/1.06  --splitting_cvd                         false
% 0.36/1.06  --splitting_cvd_svl                     false
% 0.36/1.06  --splitting_nvd                         32
% 0.36/1.06  --sub_typing                            true
% 0.36/1.06  --prep_gs_sim                           true
% 0.36/1.06  --prep_unflatten                        true
% 0.36/1.06  --prep_res_sim                          true
% 0.36/1.06  --prep_upred                            true
% 0.36/1.06  --prep_sem_filter                       exhaustive
% 0.36/1.06  --prep_sem_filter_out                   false
% 0.36/1.06  --pred_elim                             true
% 0.36/1.06  --res_sim_input                         true
% 0.36/1.06  --eq_ax_congr_red                       true
% 0.36/1.06  --pure_diseq_elim                       true
% 0.36/1.06  --brand_transform                       false
% 0.36/1.06  --non_eq_to_eq                          false
% 0.36/1.06  --prep_def_merge                        true
% 0.36/1.06  --prep_def_merge_prop_impl              false
% 0.36/1.06  --prep_def_merge_mbd                    true
% 0.36/1.06  --prep_def_merge_tr_red                 false
% 0.36/1.06  --prep_def_merge_tr_cl                  false
% 0.36/1.06  --smt_preprocessing                     true
% 0.36/1.06  --smt_ac_axioms                         fast
% 0.36/1.06  --preprocessed_out                      false
% 0.36/1.06  --preprocessed_stats                    false
% 0.36/1.06  
% 0.36/1.06  ------ Abstraction refinement Options
% 0.36/1.06  
% 0.36/1.06  --abstr_ref                             []
% 0.36/1.06  --abstr_ref_prep                        false
% 0.36/1.06  --abstr_ref_until_sat                   false
% 0.36/1.06  --abstr_ref_sig_restrict                funpre
% 0.36/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 0.36/1.06  --abstr_ref_under                       []
% 0.36/1.06  
% 0.36/1.06  ------ SAT Options
% 0.36/1.06  
% 0.36/1.06  --sat_mode                              false
% 0.36/1.06  --sat_fm_restart_options                ""
% 0.36/1.06  --sat_gr_def                            false
% 0.36/1.06  --sat_epr_types                         true
% 0.36/1.06  --sat_non_cyclic_types                  false
% 0.36/1.06  --sat_finite_models                     false
% 0.36/1.06  --sat_fm_lemmas                         false
% 0.36/1.06  --sat_fm_prep                           false
% 0.36/1.06  --sat_fm_uc_incr                        true
% 0.36/1.06  --sat_out_model                         small
% 0.36/1.06  --sat_out_clauses                       false
% 0.36/1.06  
% 0.36/1.06  ------ QBF Options
% 0.36/1.06  
% 0.36/1.06  --qbf_mode                              false
% 0.36/1.06  --qbf_elim_univ                         false
% 0.36/1.06  --qbf_dom_inst                          none
% 0.36/1.06  --qbf_dom_pre_inst                      false
% 0.36/1.06  --qbf_sk_in                             false
% 0.36/1.06  --qbf_pred_elim                         true
% 0.36/1.06  --qbf_split                             512
% 0.36/1.06  
% 0.36/1.06  ------ BMC1 Options
% 0.36/1.06  
% 0.36/1.06  --bmc1_incremental                      false
% 0.36/1.06  --bmc1_axioms                           reachable_all
% 0.36/1.06  --bmc1_min_bound                        0
% 0.36/1.06  --bmc1_max_bound                        -1
% 0.36/1.06  --bmc1_max_bound_default                -1
% 0.36/1.06  --bmc1_symbol_reachability              true
% 0.36/1.06  --bmc1_property_lemmas                  false
% 0.36/1.06  --bmc1_k_induction                      false
% 0.36/1.06  --bmc1_non_equiv_states                 false
% 0.36/1.06  --bmc1_deadlock                         false
% 0.36/1.06  --bmc1_ucm                              false
% 0.36/1.06  --bmc1_add_unsat_core                   none
% 0.36/1.06  --bmc1_unsat_core_children              false
% 0.36/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 0.36/1.06  --bmc1_out_stat                         full
% 0.36/1.06  --bmc1_ground_init                      false
% 0.36/1.06  --bmc1_pre_inst_next_state              false
% 0.36/1.06  --bmc1_pre_inst_state                   false
% 0.36/1.06  --bmc1_pre_inst_reach_state             false
% 0.36/1.06  --bmc1_out_unsat_core                   false
% 0.36/1.06  --bmc1_aig_witness_out                  false
% 0.36/1.06  --bmc1_verbose                          false
% 0.36/1.06  --bmc1_dump_clauses_tptp                false
% 0.36/1.06  --bmc1_dump_unsat_core_tptp             false
% 0.36/1.06  --bmc1_dump_file                        -
% 0.36/1.06  --bmc1_ucm_expand_uc_limit              128
% 0.36/1.06  --bmc1_ucm_n_expand_iterations          6
% 0.36/1.06  --bmc1_ucm_extend_mode                  1
% 0.36/1.06  --bmc1_ucm_init_mode                    2
% 0.36/1.06  --bmc1_ucm_cone_mode                    none
% 0.36/1.06  --bmc1_ucm_reduced_relation_type        0
% 0.36/1.06  --bmc1_ucm_relax_model                  4
% 0.36/1.06  --bmc1_ucm_full_tr_after_sat            true
% 0.36/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 0.36/1.06  --bmc1_ucm_layered_model                none
% 0.36/1.06  --bmc1_ucm_max_lemma_size               10
% 0.36/1.06  
% 0.36/1.06  ------ AIG Options
% 0.36/1.06  
% 0.36/1.06  --aig_mode                              false
% 0.36/1.06  
% 0.36/1.06  ------ Instantiation Options
% 0.36/1.06  
% 0.36/1.06  --instantiation_flag                    true
% 0.36/1.06  --inst_sos_flag                         false
% 0.36/1.06  --inst_sos_phase                        true
% 0.36/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.36/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.36/1.06  --inst_lit_sel_side                     num_symb
% 0.36/1.06  --inst_solver_per_active                1400
% 0.36/1.06  --inst_solver_calls_frac                1.
% 0.36/1.06  --inst_passive_queue_type               priority_queues
% 0.36/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.36/1.06  --inst_passive_queues_freq              [25;2]
% 0.36/1.06  --inst_dismatching                      true
% 0.36/1.06  --inst_eager_unprocessed_to_passive     true
% 0.36/1.06  --inst_prop_sim_given                   true
% 0.36/1.06  --inst_prop_sim_new                     false
% 0.36/1.06  --inst_subs_new                         false
% 0.36/1.06  --inst_eq_res_simp                      false
% 0.36/1.06  --inst_subs_given                       false
% 0.36/1.06  --inst_orphan_elimination               true
% 0.36/1.06  --inst_learning_loop_flag               true
% 0.36/1.06  --inst_learning_start                   3000
% 0.36/1.06  --inst_learning_factor                  2
% 0.36/1.06  --inst_start_prop_sim_after_learn       3
% 0.36/1.06  --inst_sel_renew                        solver
% 0.36/1.06  --inst_lit_activity_flag                true
% 0.36/1.06  --inst_restr_to_given                   false
% 0.36/1.06  --inst_activity_threshold               500
% 0.36/1.06  --inst_out_proof                        true
% 0.36/1.06  
% 0.36/1.06  ------ Resolution Options
% 0.36/1.06  
% 0.36/1.06  --resolution_flag                       true
% 0.36/1.06  --res_lit_sel                           adaptive
% 0.36/1.06  --res_lit_sel_side                      none
% 0.36/1.06  --res_ordering                          kbo
% 0.36/1.06  --res_to_prop_solver                    active
% 0.36/1.06  --res_prop_simpl_new                    false
% 0.36/1.06  --res_prop_simpl_given                  true
% 0.36/1.06  --res_passive_queue_type                priority_queues
% 0.36/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.36/1.06  --res_passive_queues_freq               [15;5]
% 0.36/1.06  --res_forward_subs                      full
% 0.36/1.06  --res_backward_subs                     full
% 0.36/1.06  --res_forward_subs_resolution           true
% 0.36/1.06  --res_backward_subs_resolution          true
% 0.36/1.06  --res_orphan_elimination                true
% 0.36/1.06  --res_time_limit                        2.
% 0.36/1.06  --res_out_proof                         true
% 0.36/1.06  
% 0.36/1.06  ------ Superposition Options
% 0.36/1.06  
% 0.36/1.06  --superposition_flag                    true
% 0.36/1.06  --sup_passive_queue_type                priority_queues
% 0.36/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.36/1.06  --sup_passive_queues_freq               [8;1;4]
% 0.36/1.06  --demod_completeness_check              fast
% 0.36/1.06  --demod_use_ground                      true
% 0.36/1.06  --sup_to_prop_solver                    passive
% 0.36/1.06  --sup_prop_simpl_new                    true
% 0.36/1.06  --sup_prop_simpl_given                  true
% 0.36/1.06  --sup_fun_splitting                     false
% 0.36/1.06  --sup_smt_interval                      50000
% 0.36/1.06  
% 0.36/1.06  ------ Superposition Simplification Setup
% 0.36/1.06  
% 0.36/1.06  --sup_indices_passive                   []
% 0.36/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 0.36/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.06  --sup_full_bw                           [BwDemod]
% 0.36/1.06  --sup_immed_triv                        [TrivRules]
% 0.36/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.36/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.06  --sup_immed_bw_main                     []
% 0.36/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 0.36/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.06  
% 0.36/1.06  ------ Combination Options
% 0.36/1.06  
% 0.36/1.06  --comb_res_mult                         3
% 0.36/1.06  --comb_sup_mult                         2
% 0.36/1.06  --comb_inst_mult                        10
% 0.36/1.06  
% 0.36/1.06  ------ Debug Options
% 0.36/1.06  
% 0.36/1.06  --dbg_backtrace                         false
% 0.36/1.06  --dbg_dump_prop_clauses                 false
% 0.36/1.06  --dbg_dump_prop_clauses_file            -
% 0.36/1.06  --dbg_out_stat                          false
% 0.36/1.06  ------ Parsing...
% 0.36/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.36/1.06  
% 0.36/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 0.36/1.06  
% 0.36/1.06  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.36/1.06  
% 0.36/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.36/1.06  ------ Proving...
% 0.36/1.06  ------ Problem Properties 
% 0.36/1.06  
% 0.36/1.06  
% 0.36/1.06  clauses                                 29
% 0.36/1.06  conjectures                             11
% 0.36/1.06  EPR                                     12
% 0.36/1.06  Horn                                    28
% 0.36/1.06  unary                                   12
% 0.36/1.06  binary                                  5
% 0.36/1.06  lits                                    80
% 0.36/1.06  lits eq                                 7
% 0.36/1.06  fd_pure                                 0
% 0.36/1.06  fd_pseudo                               0
% 0.36/1.06  fd_cond                                 0
% 0.36/1.06  fd_pseudo_cond                          1
% 0.36/1.06  AC symbols                              0
% 0.36/1.06  
% 0.36/1.06  ------ Schedule dynamic 5 is on 
% 0.36/1.06  
% 0.36/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.36/1.06  
% 0.36/1.06  
% 0.36/1.06  ------ 
% 0.36/1.06  Current options:
% 0.36/1.06  ------ 
% 0.36/1.06  
% 0.36/1.06  ------ Input Options
% 0.36/1.06  
% 0.36/1.06  --out_options                           all
% 0.36/1.06  --tptp_safe_out                         true
% 0.36/1.06  --problem_path                          ""
% 0.36/1.06  --include_path                          ""
% 0.36/1.06  --clausifier                            res/vclausify_rel
% 0.36/1.06  --clausifier_options                    --mode clausify
% 0.36/1.06  --stdin                                 false
% 0.36/1.06  --stats_out                             all
% 0.36/1.06  
% 0.36/1.06  ------ General Options
% 0.36/1.06  
% 0.36/1.06  --fof                                   false
% 0.36/1.06  --time_out_real                         305.
% 0.36/1.06  --time_out_virtual                      -1.
% 0.36/1.06  --symbol_type_check                     false
% 0.36/1.06  --clausify_out                          false
% 0.36/1.06  --sig_cnt_out                           false
% 0.36/1.06  --trig_cnt_out                          false
% 0.36/1.06  --trig_cnt_out_tolerance                1.
% 0.36/1.06  --trig_cnt_out_sk_spl                   false
% 0.36/1.06  --abstr_cl_out                          false
% 0.36/1.06  
% 0.36/1.06  ------ Global Options
% 0.36/1.06  
% 0.36/1.06  --schedule                              default
% 0.36/1.06  --add_important_lit                     false
% 0.36/1.06  --prop_solver_per_cl                    1000
% 0.36/1.06  --min_unsat_core                        false
% 0.36/1.06  --soft_assumptions                      false
% 0.36/1.06  --soft_lemma_size                       3
% 0.36/1.06  --prop_impl_unit_size                   0
% 0.36/1.06  --prop_impl_unit                        []
% 0.36/1.06  --share_sel_clauses                     true
% 0.36/1.06  --reset_solvers                         false
% 0.36/1.06  --bc_imp_inh                            [conj_cone]
% 0.36/1.06  --conj_cone_tolerance                   3.
% 0.36/1.06  --extra_neg_conj                        none
% 0.36/1.06  --large_theory_mode                     true
% 0.36/1.06  --prolific_symb_bound                   200
% 0.36/1.06  --lt_threshold                          2000
% 0.36/1.06  --clause_weak_htbl                      true
% 0.36/1.06  --gc_record_bc_elim                     false
% 0.36/1.06  
% 0.36/1.06  ------ Preprocessing Options
% 0.36/1.06  
% 0.36/1.06  --preprocessing_flag                    true
% 0.36/1.06  --time_out_prep_mult                    0.1
% 0.36/1.06  --splitting_mode                        input
% 0.36/1.06  --splitting_grd                         true
% 0.36/1.06  --splitting_cvd                         false
% 0.36/1.06  --splitting_cvd_svl                     false
% 0.36/1.06  --splitting_nvd                         32
% 0.36/1.06  --sub_typing                            true
% 0.36/1.06  --prep_gs_sim                           true
% 0.36/1.06  --prep_unflatten                        true
% 0.36/1.06  --prep_res_sim                          true
% 0.36/1.06  --prep_upred                            true
% 0.36/1.06  --prep_sem_filter                       exhaustive
% 0.36/1.06  --prep_sem_filter_out                   false
% 0.36/1.06  --pred_elim                             true
% 0.36/1.06  --res_sim_input                         true
% 0.36/1.06  --eq_ax_congr_red                       true
% 0.36/1.06  --pure_diseq_elim                       true
% 0.36/1.06  --brand_transform                       false
% 0.36/1.06  --non_eq_to_eq                          false
% 0.36/1.06  --prep_def_merge                        true
% 0.36/1.06  --prep_def_merge_prop_impl              false
% 0.36/1.06  --prep_def_merge_mbd                    true
% 0.36/1.06  --prep_def_merge_tr_red                 false
% 0.36/1.06  --prep_def_merge_tr_cl                  false
% 0.36/1.06  --smt_preprocessing                     true
% 0.36/1.06  --smt_ac_axioms                         fast
% 0.36/1.06  --preprocessed_out                      false
% 0.36/1.06  --preprocessed_stats                    false
% 0.36/1.06  
% 0.36/1.06  ------ Abstraction refinement Options
% 0.36/1.06  
% 0.36/1.06  --abstr_ref                             []
% 0.36/1.06  --abstr_ref_prep                        false
% 0.36/1.06  --abstr_ref_until_sat                   false
% 0.36/1.06  --abstr_ref_sig_restrict                funpre
% 0.36/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 0.36/1.06  --abstr_ref_under                       []
% 0.36/1.06  
% 0.36/1.06  ------ SAT Options
% 0.36/1.06  
% 0.36/1.06  --sat_mode                              false
% 0.36/1.06  --sat_fm_restart_options                ""
% 0.36/1.06  --sat_gr_def                            false
% 0.36/1.06  --sat_epr_types                         true
% 0.36/1.06  --sat_non_cyclic_types                  false
% 0.36/1.06  --sat_finite_models                     false
% 0.36/1.06  --sat_fm_lemmas                         false
% 0.36/1.06  --sat_fm_prep                           false
% 0.36/1.06  --sat_fm_uc_incr                        true
% 0.36/1.06  --sat_out_model                         small
% 0.36/1.06  --sat_out_clauses                       false
% 0.36/1.06  
% 0.36/1.06  ------ QBF Options
% 0.36/1.06  
% 0.36/1.06  --qbf_mode                              false
% 0.36/1.06  --qbf_elim_univ                         false
% 0.36/1.06  --qbf_dom_inst                          none
% 0.36/1.06  --qbf_dom_pre_inst                      false
% 0.36/1.06  --qbf_sk_in                             false
% 0.36/1.06  --qbf_pred_elim                         true
% 0.36/1.06  --qbf_split                             512
% 0.36/1.06  
% 0.36/1.06  ------ BMC1 Options
% 0.36/1.06  
% 0.36/1.06  --bmc1_incremental                      false
% 0.36/1.06  --bmc1_axioms                           reachable_all
% 0.36/1.06  --bmc1_min_bound                        0
% 0.36/1.06  --bmc1_max_bound                        -1
% 0.36/1.06  --bmc1_max_bound_default                -1
% 0.36/1.06  --bmc1_symbol_reachability              true
% 0.36/1.06  --bmc1_property_lemmas                  false
% 0.36/1.06  --bmc1_k_induction                      false
% 0.36/1.06  --bmc1_non_equiv_states                 false
% 0.36/1.06  --bmc1_deadlock                         false
% 0.36/1.06  --bmc1_ucm                              false
% 0.36/1.06  --bmc1_add_unsat_core                   none
% 0.36/1.06  --bmc1_unsat_core_children              false
% 0.36/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 0.36/1.06  --bmc1_out_stat                         full
% 0.36/1.06  --bmc1_ground_init                      false
% 0.36/1.06  --bmc1_pre_inst_next_state              false
% 0.36/1.06  --bmc1_pre_inst_state                   false
% 0.36/1.06  --bmc1_pre_inst_reach_state             false
% 0.36/1.06  --bmc1_out_unsat_core                   false
% 0.36/1.06  --bmc1_aig_witness_out                  false
% 0.36/1.06  --bmc1_verbose                          false
% 0.36/1.06  --bmc1_dump_clauses_tptp                false
% 0.36/1.06  --bmc1_dump_unsat_core_tptp             false
% 0.36/1.06  --bmc1_dump_file                        -
% 0.36/1.06  --bmc1_ucm_expand_uc_limit              128
% 0.36/1.06  --bmc1_ucm_n_expand_iterations          6
% 0.36/1.06  --bmc1_ucm_extend_mode                  1
% 0.36/1.06  --bmc1_ucm_init_mode                    2
% 0.36/1.06  --bmc1_ucm_cone_mode                    none
% 0.36/1.06  --bmc1_ucm_reduced_relation_type        0
% 0.36/1.06  --bmc1_ucm_relax_model                  4
% 0.36/1.06  --bmc1_ucm_full_tr_after_sat            true
% 0.36/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 0.36/1.06  --bmc1_ucm_layered_model                none
% 0.36/1.06  --bmc1_ucm_max_lemma_size               10
% 0.36/1.06  
% 0.36/1.06  ------ AIG Options
% 0.36/1.06  
% 0.36/1.06  --aig_mode                              false
% 0.36/1.06  
% 0.36/1.06  ------ Instantiation Options
% 0.36/1.06  
% 0.36/1.06  --instantiation_flag                    true
% 0.36/1.06  --inst_sos_flag                         false
% 0.36/1.06  --inst_sos_phase                        true
% 0.36/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.36/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.36/1.06  --inst_lit_sel_side                     none
% 0.36/1.06  --inst_solver_per_active                1400
% 0.36/1.06  --inst_solver_calls_frac                1.
% 0.36/1.06  --inst_passive_queue_type               priority_queues
% 0.36/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.36/1.06  --inst_passive_queues_freq              [25;2]
% 0.36/1.06  --inst_dismatching                      true
% 0.36/1.06  --inst_eager_unprocessed_to_passive     true
% 0.36/1.06  --inst_prop_sim_given                   true
% 0.36/1.06  --inst_prop_sim_new                     false
% 0.36/1.06  --inst_subs_new                         false
% 0.36/1.06  --inst_eq_res_simp                      false
% 0.36/1.06  --inst_subs_given                       false
% 0.36/1.06  --inst_orphan_elimination               true
% 0.36/1.06  --inst_learning_loop_flag               true
% 0.36/1.06  --inst_learning_start                   3000
% 0.36/1.06  --inst_learning_factor                  2
% 0.36/1.06  --inst_start_prop_sim_after_learn       3
% 0.36/1.06  --inst_sel_renew                        solver
% 0.36/1.06  --inst_lit_activity_flag                true
% 0.36/1.06  --inst_restr_to_given                   false
% 0.36/1.06  --inst_activity_threshold               500
% 0.36/1.06  --inst_out_proof                        true
% 0.36/1.06  
% 0.36/1.06  ------ Resolution Options
% 0.36/1.06  
% 0.36/1.06  --resolution_flag                       false
% 0.36/1.06  --res_lit_sel                           adaptive
% 0.36/1.06  --res_lit_sel_side                      none
% 0.36/1.06  --res_ordering                          kbo
% 0.36/1.06  --res_to_prop_solver                    active
% 0.36/1.06  --res_prop_simpl_new                    false
% 0.36/1.06  --res_prop_simpl_given                  true
% 0.36/1.06  --res_passive_queue_type                priority_queues
% 0.36/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.36/1.06  --res_passive_queues_freq               [15;5]
% 0.36/1.06  --res_forward_subs                      full
% 0.36/1.06  --res_backward_subs                     full
% 0.36/1.06  --res_forward_subs_resolution           true
% 0.36/1.06  --res_backward_subs_resolution          true
% 0.36/1.06  --res_orphan_elimination                true
% 0.36/1.06  --res_time_limit                        2.
% 0.36/1.06  --res_out_proof                         true
% 0.36/1.06  
% 0.36/1.06  ------ Superposition Options
% 0.36/1.06  
% 0.36/1.06  --superposition_flag                    true
% 0.36/1.06  --sup_passive_queue_type                priority_queues
% 0.36/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.36/1.06  --sup_passive_queues_freq               [8;1;4]
% 0.36/1.06  --demod_completeness_check              fast
% 0.36/1.06  --demod_use_ground                      true
% 0.36/1.06  --sup_to_prop_solver                    passive
% 0.36/1.06  --sup_prop_simpl_new                    true
% 0.36/1.06  --sup_prop_simpl_given                  true
% 0.36/1.06  --sup_fun_splitting                     false
% 0.36/1.06  --sup_smt_interval                      50000
% 0.36/1.06  
% 0.36/1.06  ------ Superposition Simplification Setup
% 0.36/1.06  
% 0.36/1.06  --sup_indices_passive                   []
% 0.36/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 0.36/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.06  --sup_full_bw                           [BwDemod]
% 0.36/1.06  --sup_immed_triv                        [TrivRules]
% 0.36/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.36/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.06  --sup_immed_bw_main                     []
% 0.36/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 0.36/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.06  
% 0.36/1.06  ------ Combination Options
% 0.36/1.06  
% 0.36/1.06  --comb_res_mult                         3
% 0.36/1.06  --comb_sup_mult                         2
% 0.36/1.06  --comb_inst_mult                        10
% 0.36/1.06  
% 0.36/1.06  ------ Debug Options
% 0.36/1.06  
% 0.36/1.06  --dbg_backtrace                         false
% 0.36/1.06  --dbg_dump_prop_clauses                 false
% 0.36/1.06  --dbg_dump_prop_clauses_file            -
% 0.36/1.06  --dbg_out_stat                          false
% 0.36/1.06  
% 0.36/1.06  
% 0.36/1.06  
% 0.36/1.06  
% 0.36/1.06  ------ Proving...
% 0.36/1.06  
% 0.36/1.06  
% 0.36/1.06  % SZS status Theorem for theBenchmark.p
% 0.36/1.06  
% 0.36/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 0.36/1.06  
% 0.36/1.06  fof(f19,conjecture,(
% 0.36/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f20,negated_conjecture,(
% 0.36/1.06    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 0.36/1.06    inference(negated_conjecture,[],[f19])).
% 0.36/1.06  
% 0.36/1.06  fof(f49,plain,(
% 0.36/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.36/1.06    inference(ennf_transformation,[],[f20])).
% 0.36/1.06  
% 0.36/1.06  fof(f50,plain,(
% 0.36/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.36/1.06    inference(flattening,[],[f49])).
% 0.36/1.06  
% 0.36/1.06  fof(f60,plain,(
% 0.36/1.06    ( ! [X2,X0,X1] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 0.36/1.06    introduced(choice_axiom,[])).
% 0.36/1.06  
% 0.36/1.06  fof(f59,plain,(
% 0.36/1.06    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 0.36/1.06    introduced(choice_axiom,[])).
% 0.36/1.06  
% 0.36/1.06  fof(f58,plain,(
% 0.36/1.06    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 0.36/1.06    introduced(choice_axiom,[])).
% 0.36/1.06  
% 0.36/1.06  fof(f57,plain,(
% 0.36/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.36/1.06    introduced(choice_axiom,[])).
% 0.36/1.06  
% 0.36/1.06  fof(f61,plain,(
% 0.36/1.06    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.36/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f50,f60,f59,f58,f57])).
% 0.36/1.06  
% 0.36/1.06  fof(f93,plain,(
% 0.36/1.06    m1_pre_topc(sK2,sK1)),
% 0.36/1.06    inference(cnf_transformation,[],[f61])).
% 0.36/1.06  
% 0.36/1.06  fof(f13,axiom,(
% 0.36/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f39,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.36/1.06    inference(ennf_transformation,[],[f13])).
% 0.36/1.06  
% 0.36/1.06  fof(f53,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.36/1.06    inference(nnf_transformation,[],[f39])).
% 0.36/1.06  
% 0.36/1.06  fof(f76,plain,(
% 0.36/1.06    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f53])).
% 0.36/1.06  
% 0.36/1.06  fof(f8,axiom,(
% 0.36/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f32,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.36/1.06    inference(ennf_transformation,[],[f8])).
% 0.36/1.06  
% 0.36/1.06  fof(f71,plain,(
% 0.36/1.06    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f32])).
% 0.36/1.06  
% 0.36/1.06  fof(f97,plain,(
% 0.36/1.06    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.36/1.06    inference(cnf_transformation,[],[f61])).
% 0.36/1.06  
% 0.36/1.06  fof(f12,axiom,(
% 0.36/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f38,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.36/1.06    inference(ennf_transformation,[],[f12])).
% 0.36/1.06  
% 0.36/1.06  fof(f75,plain,(
% 0.36/1.06    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f38])).
% 0.36/1.06  
% 0.36/1.06  fof(f91,plain,(
% 0.36/1.06    l1_pre_topc(sK1)),
% 0.36/1.06    inference(cnf_transformation,[],[f61])).
% 0.36/1.06  
% 0.36/1.06  fof(f17,axiom,(
% 0.36/1.06    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f46,plain,(
% 0.36/1.06    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.36/1.06    inference(ennf_transformation,[],[f17])).
% 0.36/1.06  
% 0.36/1.06  fof(f83,plain,(
% 0.36/1.06    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f46])).
% 0.36/1.06  
% 0.36/1.06  fof(f18,axiom,(
% 0.36/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f47,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.36/1.06    inference(ennf_transformation,[],[f18])).
% 0.36/1.06  
% 0.36/1.06  fof(f48,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.36/1.06    inference(flattening,[],[f47])).
% 0.36/1.06  
% 0.36/1.06  fof(f56,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.36/1.06    inference(nnf_transformation,[],[f48])).
% 0.36/1.06  
% 0.36/1.06  fof(f85,plain,(
% 0.36/1.06    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f56])).
% 0.36/1.06  
% 0.36/1.06  fof(f1,axiom,(
% 0.36/1.06    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f51,plain,(
% 0.36/1.06    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.36/1.06    inference(nnf_transformation,[],[f1])).
% 0.36/1.06  
% 0.36/1.06  fof(f52,plain,(
% 0.36/1.06    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.36/1.06    inference(flattening,[],[f51])).
% 0.36/1.06  
% 0.36/1.06  fof(f64,plain,(
% 0.36/1.06    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f52])).
% 0.36/1.06  
% 0.36/1.06  fof(f90,plain,(
% 0.36/1.06    v2_pre_topc(sK1)),
% 0.36/1.06    inference(cnf_transformation,[],[f61])).
% 0.36/1.06  
% 0.36/1.06  fof(f11,axiom,(
% 0.36/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f22,plain,(
% 0.36/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 0.36/1.06    inference(pure_predicate_removal,[],[f11])).
% 0.36/1.06  
% 0.36/1.06  fof(f36,plain,(
% 0.36/1.06    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.36/1.06    inference(ennf_transformation,[],[f22])).
% 0.36/1.06  
% 0.36/1.06  fof(f37,plain,(
% 0.36/1.06    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.36/1.06    inference(flattening,[],[f36])).
% 0.36/1.06  
% 0.36/1.06  fof(f74,plain,(
% 0.36/1.06    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f37])).
% 0.36/1.06  
% 0.36/1.06  fof(f9,axiom,(
% 0.36/1.06    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f33,plain,(
% 0.36/1.06    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.36/1.06    inference(ennf_transformation,[],[f9])).
% 0.36/1.06  
% 0.36/1.06  fof(f72,plain,(
% 0.36/1.06    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f33])).
% 0.36/1.06  
% 0.36/1.06  fof(f6,axiom,(
% 0.36/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f21,plain,(
% 0.36/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 0.36/1.06    inference(pure_predicate_removal,[],[f6])).
% 0.36/1.06  
% 0.36/1.06  fof(f30,plain,(
% 0.36/1.06    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.36/1.06    inference(ennf_transformation,[],[f21])).
% 0.36/1.06  
% 0.36/1.06  fof(f69,plain,(
% 0.36/1.06    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.36/1.06    inference(cnf_transformation,[],[f30])).
% 0.36/1.06  
% 0.36/1.06  fof(f16,axiom,(
% 0.36/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f44,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 0.36/1.06    inference(ennf_transformation,[],[f16])).
% 0.36/1.06  
% 0.36/1.06  fof(f45,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.36/1.06    inference(flattening,[],[f44])).
% 0.36/1.06  
% 0.36/1.06  fof(f55,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.36/1.06    inference(nnf_transformation,[],[f45])).
% 0.36/1.06  
% 0.36/1.06  fof(f81,plain,(
% 0.36/1.06    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f55])).
% 0.36/1.06  
% 0.36/1.06  fof(f103,plain,(
% 0.36/1.06    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 0.36/1.06    inference(equality_resolution,[],[f81])).
% 0.36/1.06  
% 0.36/1.06  fof(f96,plain,(
% 0.36/1.06    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.36/1.06    inference(cnf_transformation,[],[f61])).
% 0.36/1.06  
% 0.36/1.06  fof(f15,axiom,(
% 0.36/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f42,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.36/1.06    inference(ennf_transformation,[],[f15])).
% 0.36/1.06  
% 0.36/1.06  fof(f43,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.36/1.06    inference(flattening,[],[f42])).
% 0.36/1.06  
% 0.36/1.06  fof(f80,plain,(
% 0.36/1.06    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f43])).
% 0.36/1.06  
% 0.36/1.06  fof(f94,plain,(
% 0.36/1.06    v1_funct_1(sK3)),
% 0.36/1.06    inference(cnf_transformation,[],[f61])).
% 0.36/1.06  
% 0.36/1.06  fof(f5,axiom,(
% 0.36/1.06    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f28,plain,(
% 0.36/1.06    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.36/1.06    inference(ennf_transformation,[],[f5])).
% 0.36/1.06  
% 0.36/1.06  fof(f29,plain,(
% 0.36/1.06    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.36/1.06    inference(flattening,[],[f28])).
% 0.36/1.06  
% 0.36/1.06  fof(f68,plain,(
% 0.36/1.06    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f29])).
% 0.36/1.06  
% 0.36/1.06  fof(f86,plain,(
% 0.36/1.06    ~v2_struct_0(sK0)),
% 0.36/1.06    inference(cnf_transformation,[],[f61])).
% 0.36/1.06  
% 0.36/1.06  fof(f87,plain,(
% 0.36/1.06    v2_pre_topc(sK0)),
% 0.36/1.06    inference(cnf_transformation,[],[f61])).
% 0.36/1.06  
% 0.36/1.06  fof(f88,plain,(
% 0.36/1.06    l1_pre_topc(sK0)),
% 0.36/1.06    inference(cnf_transformation,[],[f61])).
% 0.36/1.06  
% 0.36/1.06  fof(f89,plain,(
% 0.36/1.06    ~v2_struct_0(sK1)),
% 0.36/1.06    inference(cnf_transformation,[],[f61])).
% 0.36/1.06  
% 0.36/1.06  fof(f95,plain,(
% 0.36/1.06    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.36/1.06    inference(cnf_transformation,[],[f61])).
% 0.36/1.06  
% 0.36/1.06  fof(f7,axiom,(
% 0.36/1.06    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f31,plain,(
% 0.36/1.06    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.36/1.06    inference(ennf_transformation,[],[f7])).
% 0.36/1.06  
% 0.36/1.06  fof(f70,plain,(
% 0.36/1.06    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f31])).
% 0.36/1.06  
% 0.36/1.06  fof(f10,axiom,(
% 0.36/1.06    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f34,plain,(
% 0.36/1.06    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.36/1.06    inference(ennf_transformation,[],[f10])).
% 0.36/1.06  
% 0.36/1.06  fof(f35,plain,(
% 0.36/1.06    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.36/1.06    inference(flattening,[],[f34])).
% 0.36/1.06  
% 0.36/1.06  fof(f73,plain,(
% 0.36/1.06    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f35])).
% 0.36/1.06  
% 0.36/1.06  fof(f14,axiom,(
% 0.36/1.06    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f40,plain,(
% 0.36/1.06    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 0.36/1.06    inference(ennf_transformation,[],[f14])).
% 0.36/1.06  
% 0.36/1.06  fof(f41,plain,(
% 0.36/1.06    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.36/1.06    inference(flattening,[],[f40])).
% 0.36/1.06  
% 0.36/1.06  fof(f54,plain,(
% 0.36/1.06    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.36/1.06    inference(nnf_transformation,[],[f41])).
% 0.36/1.06  
% 0.36/1.06  fof(f79,plain,(
% 0.36/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f54])).
% 0.36/1.06  
% 0.36/1.06  fof(f101,plain,(
% 0.36/1.06    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 0.36/1.06    inference(equality_resolution,[],[f79])).
% 0.36/1.06  
% 0.36/1.06  fof(f98,plain,(
% 0.36/1.06    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.36/1.06    inference(cnf_transformation,[],[f61])).
% 0.36/1.06  
% 0.36/1.06  fof(f4,axiom,(
% 0.36/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f23,plain,(
% 0.36/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.36/1.06    inference(pure_predicate_removal,[],[f4])).
% 0.36/1.06  
% 0.36/1.06  fof(f27,plain,(
% 0.36/1.06    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.36/1.06    inference(ennf_transformation,[],[f23])).
% 0.36/1.06  
% 0.36/1.06  fof(f67,plain,(
% 0.36/1.06    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.36/1.06    inference(cnf_transformation,[],[f27])).
% 0.36/1.06  
% 0.36/1.06  fof(f2,axiom,(
% 0.36/1.06    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f24,plain,(
% 0.36/1.06    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.36/1.06    inference(ennf_transformation,[],[f2])).
% 0.36/1.06  
% 0.36/1.06  fof(f25,plain,(
% 0.36/1.06    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.36/1.06    inference(flattening,[],[f24])).
% 0.36/1.06  
% 0.36/1.06  fof(f65,plain,(
% 0.36/1.06    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f25])).
% 0.36/1.06  
% 0.36/1.06  fof(f3,axiom,(
% 0.36/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f26,plain,(
% 0.36/1.06    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.36/1.06    inference(ennf_transformation,[],[f3])).
% 0.36/1.06  
% 0.36/1.06  fof(f66,plain,(
% 0.36/1.06    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.36/1.06    inference(cnf_transformation,[],[f26])).
% 0.36/1.06  
% 0.36/1.06  cnf(c_29,negated_conjecture,
% 0.36/1.06      ( m1_pre_topc(sK2,sK1) ),
% 0.36/1.06      inference(cnf_transformation,[],[f93]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1346,plain,
% 0.36/1.06      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_15,plain,
% 0.36/1.06      ( ~ m1_pre_topc(X0,X1)
% 0.36/1.06      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 0.36/1.06      | ~ l1_pre_topc(X0)
% 0.36/1.06      | ~ l1_pre_topc(X1) ),
% 0.36/1.06      inference(cnf_transformation,[],[f76]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_9,plain,
% 0.36/1.06      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 0.36/1.06      inference(cnf_transformation,[],[f71]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_214,plain,
% 0.36/1.06      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 0.36/1.06      | ~ m1_pre_topc(X0,X1)
% 0.36/1.06      | ~ l1_pre_topc(X1) ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_15,c_9]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_215,plain,
% 0.36/1.06      ( ~ m1_pre_topc(X0,X1)
% 0.36/1.06      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 0.36/1.06      | ~ l1_pre_topc(X1) ),
% 0.36/1.06      inference(renaming,[status(thm)],[c_214]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1336,plain,
% 0.36/1.06      ( m1_pre_topc(X0,X1) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 0.36/1.06      | l1_pre_topc(X1) != iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_25,negated_conjecture,
% 0.36/1.06      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 0.36/1.06      inference(cnf_transformation,[],[f97]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_13,plain,
% 0.36/1.06      ( m1_pre_topc(X0,X1)
% 0.36/1.06      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 0.36/1.06      | ~ l1_pre_topc(X1) ),
% 0.36/1.06      inference(cnf_transformation,[],[f75]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1352,plain,
% 0.36/1.06      ( m1_pre_topc(X0,X1) = iProver_top
% 0.36/1.06      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 0.36/1.06      | l1_pre_topc(X1) != iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_2863,plain,
% 0.36/1.06      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK2) = iProver_top
% 0.36/1.06      | l1_pre_topc(sK2) != iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_25,c_1352]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_31,negated_conjecture,
% 0.36/1.06      ( l1_pre_topc(sK1) ),
% 0.36/1.06      inference(cnf_transformation,[],[f91]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_42,plain,
% 0.36/1.06      ( l1_pre_topc(sK1) = iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1355,plain,
% 0.36/1.06      ( m1_pre_topc(X0,X1) != iProver_top
% 0.36/1.06      | l1_pre_topc(X1) != iProver_top
% 0.36/1.06      | l1_pre_topc(X0) = iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_2326,plain,
% 0.36/1.06      ( l1_pre_topc(sK2) = iProver_top
% 0.36/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_1346,c_1355]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_3006,plain,
% 0.36/1.06      ( m1_pre_topc(X0,sK2) = iProver_top
% 0.36/1.06      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_2863,c_42,c_2326]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_3007,plain,
% 0.36/1.06      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK2) = iProver_top ),
% 0.36/1.06      inference(renaming,[status(thm)],[c_3006]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_3014,plain,
% 0.36/1.06      ( m1_pre_topc(X0,sK2) = iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK1) != iProver_top
% 0.36/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_1336,c_3007]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_3121,plain,
% 0.36/1.06      ( m1_pre_topc(X0,sK1) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK2) = iProver_top ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_3014,c_42]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_3122,plain,
% 0.36/1.06      ( m1_pre_topc(X0,sK2) = iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK1) != iProver_top ),
% 0.36/1.06      inference(renaming,[status(thm)],[c_3121]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_3130,plain,
% 0.36/1.06      ( m1_pre_topc(sK2,sK2) = iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_1346,c_3122]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_21,plain,
% 0.36/1.06      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 0.36/1.06      inference(cnf_transformation,[],[f83]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1351,plain,
% 0.36/1.06      ( m1_pre_topc(X0,X0) = iProver_top
% 0.36/1.06      | l1_pre_topc(X0) != iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_3129,plain,
% 0.36/1.06      ( m1_pre_topc(sK1,sK2) = iProver_top
% 0.36/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_1351,c_3122]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_53,plain,
% 0.36/1.06      ( m1_pre_topc(X0,X0) = iProver_top
% 0.36/1.06      | l1_pre_topc(X0) != iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_55,plain,
% 0.36/1.06      ( m1_pre_topc(sK1,sK1) = iProver_top
% 0.36/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 0.36/1.06      inference(instantiation,[status(thm)],[c_53]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_70,plain,
% 0.36/1.06      ( m1_pre_topc(X0,X1) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 0.36/1.06      | l1_pre_topc(X1) != iProver_top
% 0.36/1.06      | l1_pre_topc(X0) != iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_72,plain,
% 0.36/1.06      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 0.36/1.06      | m1_pre_topc(sK1,sK1) != iProver_top
% 0.36/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 0.36/1.06      inference(instantiation,[status(thm)],[c_70]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_2880,plain,
% 0.36/1.06      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 0.36/1.06      | m1_pre_topc(sK1,sK2) = iProver_top
% 0.36/1.06      | l1_pre_topc(sK2) != iProver_top ),
% 0.36/1.06      inference(instantiation,[status(thm)],[c_2863]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_3402,plain,
% 0.36/1.06      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_3129,c_42,c_55,c_72,c_2326,c_2880]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_22,plain,
% 0.36/1.06      ( ~ m1_pre_topc(X0,X1)
% 0.36/1.06      | ~ m1_pre_topc(X2,X1)
% 0.36/1.06      | ~ m1_pre_topc(X0,X2)
% 0.36/1.06      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 0.36/1.06      | ~ v2_pre_topc(X1)
% 0.36/1.06      | ~ l1_pre_topc(X1) ),
% 0.36/1.06      inference(cnf_transformation,[],[f85]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1350,plain,
% 0.36/1.06      ( m1_pre_topc(X0,X1) != iProver_top
% 0.36/1.06      | m1_pre_topc(X2,X1) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,X2) != iProver_top
% 0.36/1.06      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 0.36/1.06      | v2_pre_topc(X1) != iProver_top
% 0.36/1.06      | l1_pre_topc(X1) != iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_3720,plain,
% 0.36/1.06      ( m1_pre_topc(X0,sK2) != iProver_top
% 0.36/1.06      | m1_pre_topc(sK1,X0) != iProver_top
% 0.36/1.06      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
% 0.36/1.06      | v2_pre_topc(sK2) != iProver_top
% 0.36/1.06      | l1_pre_topc(sK2) != iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_3402,c_1350]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_6368,plain,
% 0.36/1.06      ( v2_pre_topc(sK2) != iProver_top
% 0.36/1.06      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
% 0.36/1.06      | m1_pre_topc(sK1,X0) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK2) != iProver_top ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_3720,c_42,c_2326]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_6369,plain,
% 0.36/1.06      ( m1_pre_topc(X0,sK2) != iProver_top
% 0.36/1.06      | m1_pre_topc(sK1,X0) != iProver_top
% 0.36/1.06      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
% 0.36/1.06      | v2_pre_topc(sK2) != iProver_top ),
% 0.36/1.06      inference(renaming,[status(thm)],[c_6368]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_0,plain,
% 0.36/1.06      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 0.36/1.06      inference(cnf_transformation,[],[f64]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1358,plain,
% 0.36/1.06      ( X0 = X1
% 0.36/1.06      | r1_tarski(X0,X1) != iProver_top
% 0.36/1.06      | r1_tarski(X1,X0) != iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_6376,plain,
% 0.36/1.06      ( u1_struct_0(X0) = u1_struct_0(sK1)
% 0.36/1.06      | m1_pre_topc(X0,sK2) != iProver_top
% 0.36/1.06      | m1_pre_topc(sK1,X0) != iProver_top
% 0.36/1.06      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) != iProver_top
% 0.36/1.06      | v2_pre_topc(sK2) != iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_6369,c_1358]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_2718,plain,
% 0.36/1.06      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK2) != iProver_top
% 0.36/1.06      | l1_pre_topc(sK2) != iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_25,c_1336]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_2981,plain,
% 0.36/1.06      ( m1_pre_topc(X0,sK2) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_2718,c_42,c_2326]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_2982,plain,
% 0.36/1.06      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK2) != iProver_top ),
% 0.36/1.06      inference(renaming,[status(thm)],[c_2981]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_2990,plain,
% 0.36/1.06      ( m1_pre_topc(X0,sK2) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK1) = iProver_top
% 0.36/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_2982,c_1352]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_3111,plain,
% 0.36/1.06      ( m1_pre_topc(X0,sK1) = iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK2) != iProver_top ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_2990,c_42]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_3112,plain,
% 0.36/1.06      ( m1_pre_topc(X0,sK2) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK1) = iProver_top ),
% 0.36/1.06      inference(renaming,[status(thm)],[c_3111]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_3719,plain,
% 0.36/1.06      ( m1_pre_topc(X0,X1) != iProver_top
% 0.36/1.06      | m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK2) != iProver_top
% 0.36/1.06      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 0.36/1.06      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 0.36/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_2982,c_1350]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_32,negated_conjecture,
% 0.36/1.06      ( v2_pre_topc(sK1) ),
% 0.36/1.06      inference(cnf_transformation,[],[f90]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_41,plain,
% 0.36/1.06      ( v2_pre_topc(sK1) = iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_12,plain,
% 0.36/1.06      ( ~ v2_pre_topc(X0)
% 0.36/1.06      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 0.36/1.06      | ~ l1_pre_topc(X0) ),
% 0.36/1.06      inference(cnf_transformation,[],[f74]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_75,plain,
% 0.36/1.06      ( v2_pre_topc(X0) != iProver_top
% 0.36/1.06      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 0.36/1.06      | l1_pre_topc(X0) != iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_77,plain,
% 0.36/1.06      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 0.36/1.06      | v2_pre_topc(sK1) != iProver_top
% 0.36/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 0.36/1.06      inference(instantiation,[status(thm)],[c_75]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_10,plain,
% 0.36/1.06      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 0.36/1.06      | ~ l1_pre_topc(X0) ),
% 0.36/1.06      inference(cnf_transformation,[],[f72]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_81,plain,
% 0.36/1.06      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 0.36/1.06      | l1_pre_topc(X0) != iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_83,plain,
% 0.36/1.06      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 0.36/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 0.36/1.06      inference(instantiation,[status(thm)],[c_81]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_7,plain,
% 0.36/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 0.36/1.06      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 0.36/1.06      inference(cnf_transformation,[],[f69]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1596,plain,
% 0.36/1.06      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 0.36/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 0.36/1.06      inference(instantiation,[status(thm)],[c_7]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1597,plain,
% 0.36/1.06      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 0.36/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_1596]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1599,plain,
% 0.36/1.06      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 0.36/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 0.36/1.06      inference(instantiation,[status(thm)],[c_1597]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_4467,plain,
% 0.36/1.06      ( m1_pre_topc(X0,X1) != iProver_top
% 0.36/1.06      | m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK2) != iProver_top
% 0.36/1.06      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_3719,c_41,c_42,c_77,c_83,c_1599]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_4478,plain,
% 0.36/1.06      ( m1_pre_topc(X0,X1) != iProver_top
% 0.36/1.06      | m1_pre_topc(X1,sK2) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK2) != iProver_top
% 0.36/1.06      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_2982,c_4467]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_3015,plain,
% 0.36/1.06      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 0.36/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_1351,c_3007]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_3216,plain,
% 0.36/1.06      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_3015,c_42,c_83,c_1599]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_20,plain,
% 0.36/1.06      ( m1_pre_topc(X0,X1)
% 0.36/1.06      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 0.36/1.06      | ~ v2_pre_topc(X0)
% 0.36/1.06      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 0.36/1.06      | ~ l1_pre_topc(X1)
% 0.36/1.06      | ~ l1_pre_topc(X0)
% 0.36/1.06      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 0.36/1.06      inference(cnf_transformation,[],[f103]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_198,plain,
% 0.36/1.06      ( ~ v2_pre_topc(X0)
% 0.36/1.06      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 0.36/1.06      | m1_pre_topc(X0,X1)
% 0.36/1.06      | ~ l1_pre_topc(X1)
% 0.36/1.06      | ~ l1_pre_topc(X0)
% 0.36/1.06      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_20,c_12]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_199,plain,
% 0.36/1.06      ( m1_pre_topc(X0,X1)
% 0.36/1.06      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 0.36/1.06      | ~ v2_pre_topc(X0)
% 0.36/1.06      | ~ l1_pre_topc(X0)
% 0.36/1.06      | ~ l1_pre_topc(X1)
% 0.36/1.06      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 0.36/1.06      inference(renaming,[status(thm)],[c_198]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1338,plain,
% 0.36/1.06      ( m1_pre_topc(X0,X1) = iProver_top
% 0.36/1.06      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 0.36/1.06      | v2_pre_topc(X0) != iProver_top
% 0.36/1.06      | l1_pre_topc(X1) != iProver_top
% 0.36/1.06      | l1_pre_topc(X0) != iProver_top
% 0.36/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_199]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1481,plain,
% 0.36/1.06      ( m1_pre_topc(X0,X1) = iProver_top
% 0.36/1.06      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 0.36/1.06      | v2_pre_topc(X0) != iProver_top
% 0.36/1.06      | l1_pre_topc(X1) != iProver_top
% 0.36/1.06      | l1_pre_topc(X0) != iProver_top ),
% 0.36/1.06      inference(forward_subsumption_resolution,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_1338,c_1355]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_4649,plain,
% 0.36/1.06      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 0.36/1.06      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) != iProver_top
% 0.36/1.06      | v2_pre_topc(X0) != iProver_top
% 0.36/1.06      | l1_pre_topc(X0) != iProver_top
% 0.36/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_2982,c_1481]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_5508,plain,
% 0.36/1.06      ( l1_pre_topc(X0) != iProver_top
% 0.36/1.06      | v2_pre_topc(X0) != iProver_top
% 0.36/1.06      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_4649,c_42,c_83,c_1599]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_5509,plain,
% 0.36/1.06      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 0.36/1.06      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) != iProver_top
% 0.36/1.06      | v2_pre_topc(X0) != iProver_top
% 0.36/1.06      | l1_pre_topc(X0) != iProver_top ),
% 0.36/1.06      inference(renaming,[status(thm)],[c_5508]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_5520,plain,
% 0.36/1.06      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 0.36/1.06      | v2_pre_topc(sK1) != iProver_top
% 0.36/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_3216,c_5509]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_7620,plain,
% 0.36/1.06      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_5520,c_42,c_55,c_72]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_7635,plain,
% 0.36/1.06      ( m1_pre_topc(X0,sK2) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK1) != iProver_top
% 0.36/1.06      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_7620,c_4467]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_4647,plain,
% 0.36/1.06      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 0.36/1.06      | v2_pre_topc(X0) != iProver_top
% 0.36/1.06      | l1_pre_topc(X0) != iProver_top
% 0.36/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_1351,c_1481]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1354,plain,
% 0.36/1.06      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 0.36/1.06      | l1_pre_topc(X0) != iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1356,plain,
% 0.36/1.06      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 0.36/1.06      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_2317,plain,
% 0.36/1.06      ( l1_pre_topc(X0) != iProver_top
% 0.36/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_1354,c_1356]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_6098,plain,
% 0.36/1.06      ( l1_pre_topc(X0) != iProver_top
% 0.36/1.06      | v2_pre_topc(X0) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_4647,c_2317]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_6099,plain,
% 0.36/1.06      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 0.36/1.06      | v2_pre_topc(X0) != iProver_top
% 0.36/1.06      | l1_pre_topc(X0) != iProver_top ),
% 0.36/1.06      inference(renaming,[status(thm)],[c_6098]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_6120,plain,
% 0.36/1.06      ( m1_pre_topc(X0,sK2) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK1) != iProver_top
% 0.36/1.06      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top
% 0.36/1.06      | v2_pre_topc(sK1) != iProver_top
% 0.36/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_6099,c_4467]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_7668,plain,
% 0.36/1.06      ( m1_pre_topc(X0,sK1) != iProver_top
% 0.36/1.06      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_7635,c_41,c_42,c_3014,c_6120]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_7674,plain,
% 0.36/1.06      ( u1_struct_0(X0) = u1_struct_0(sK1)
% 0.36/1.06      | m1_pre_topc(X0,sK1) != iProver_top
% 0.36/1.06      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) != iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_7668,c_1358]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_8073,plain,
% 0.36/1.06      ( u1_struct_0(X0) = u1_struct_0(sK1)
% 0.36/1.06      | m1_pre_topc(X0,sK2) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK1) != iProver_top
% 0.36/1.06      | m1_pre_topc(sK1,X0) != iProver_top
% 0.36/1.06      | m1_pre_topc(sK1,sK2) != iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_4478,c_7674]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_8109,plain,
% 0.36/1.06      ( u1_struct_0(X0) = u1_struct_0(sK1)
% 0.36/1.06      | m1_pre_topc(X0,sK2) != iProver_top
% 0.36/1.06      | m1_pre_topc(sK1,X0) != iProver_top ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_6376,c_42,c_55,c_72,c_2326,c_2880,c_2990,c_8073]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_8121,plain,
% 0.36/1.06      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 0.36/1.06      | m1_pre_topc(sK1,sK2) != iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_3130,c_8109]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_8315,plain,
% 0.36/1.06      ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_8121,c_42,c_55,c_72,c_2326,c_2880]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_26,negated_conjecture,
% 0.36/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 0.36/1.06      inference(cnf_transformation,[],[f96]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1348,plain,
% 0.36/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_18,plain,
% 0.36/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 0.36/1.06      | ~ m1_pre_topc(X3,X1)
% 0.36/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 0.36/1.06      | ~ v2_pre_topc(X1)
% 0.36/1.06      | ~ v2_pre_topc(X2)
% 0.36/1.06      | v2_struct_0(X1)
% 0.36/1.06      | v2_struct_0(X2)
% 0.36/1.06      | ~ l1_pre_topc(X1)
% 0.36/1.06      | ~ l1_pre_topc(X2)
% 0.36/1.06      | ~ v1_funct_1(X0)
% 0.36/1.06      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 0.36/1.06      inference(cnf_transformation,[],[f80]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_28,negated_conjecture,
% 0.36/1.06      ( v1_funct_1(sK3) ),
% 0.36/1.06      inference(cnf_transformation,[],[f94]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_514,plain,
% 0.36/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 0.36/1.06      | ~ m1_pre_topc(X3,X1)
% 0.36/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 0.36/1.06      | ~ v2_pre_topc(X1)
% 0.36/1.06      | ~ v2_pre_topc(X2)
% 0.36/1.06      | v2_struct_0(X1)
% 0.36/1.06      | v2_struct_0(X2)
% 0.36/1.06      | ~ l1_pre_topc(X1)
% 0.36/1.06      | ~ l1_pre_topc(X2)
% 0.36/1.06      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 0.36/1.06      | sK3 != X0 ),
% 0.36/1.06      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_515,plain,
% 0.36/1.06      ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
% 0.36/1.06      | ~ m1_pre_topc(X2,X0)
% 0.36/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 0.36/1.06      | ~ v2_pre_topc(X0)
% 0.36/1.06      | ~ v2_pre_topc(X1)
% 0.36/1.06      | v2_struct_0(X0)
% 0.36/1.06      | v2_struct_0(X1)
% 0.36/1.06      | ~ l1_pre_topc(X0)
% 0.36/1.06      | ~ l1_pre_topc(X1)
% 0.36/1.06      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2) ),
% 0.36/1.06      inference(unflattening,[status(thm)],[c_514]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1334,plain,
% 0.36/1.06      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2)
% 0.36/1.06      | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 0.36/1.06      | m1_pre_topc(X2,X0) != iProver_top
% 0.36/1.06      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 0.36/1.06      | v2_pre_topc(X1) != iProver_top
% 0.36/1.06      | v2_pre_topc(X0) != iProver_top
% 0.36/1.06      | v2_struct_0(X1) = iProver_top
% 0.36/1.06      | v2_struct_0(X0) = iProver_top
% 0.36/1.06      | l1_pre_topc(X1) != iProver_top
% 0.36/1.06      | l1_pre_topc(X0) != iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_515]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_2004,plain,
% 0.36/1.06      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 0.36/1.06      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK1) != iProver_top
% 0.36/1.06      | v2_pre_topc(sK0) != iProver_top
% 0.36/1.06      | v2_pre_topc(sK1) != iProver_top
% 0.36/1.06      | v2_struct_0(sK0) = iProver_top
% 0.36/1.06      | v2_struct_0(sK1) = iProver_top
% 0.36/1.06      | l1_pre_topc(sK0) != iProver_top
% 0.36/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_1348,c_1334]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_6,plain,
% 0.36/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.36/1.06      | ~ v1_funct_1(X0)
% 0.36/1.06      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 0.36/1.06      inference(cnf_transformation,[],[f68]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_550,plain,
% 0.36/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.36/1.06      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 0.36/1.06      | sK3 != X0 ),
% 0.36/1.06      inference(resolution_lifted,[status(thm)],[c_6,c_28]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_551,plain,
% 0.36/1.06      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.36/1.06      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 0.36/1.06      inference(unflattening,[status(thm)],[c_550]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1333,plain,
% 0.36/1.06      ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 0.36/1.06      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_551]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1826,plain,
% 0.36/1.06      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_1348,c_1333]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_2005,plain,
% 0.36/1.06      ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
% 0.36/1.06      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 0.36/1.06      | m1_pre_topc(X0,sK1) != iProver_top
% 0.36/1.06      | v2_pre_topc(sK0) != iProver_top
% 0.36/1.06      | v2_pre_topc(sK1) != iProver_top
% 0.36/1.06      | v2_struct_0(sK0) = iProver_top
% 0.36/1.06      | v2_struct_0(sK1) = iProver_top
% 0.36/1.06      | l1_pre_topc(sK0) != iProver_top
% 0.36/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 0.36/1.06      inference(demodulation,[status(thm)],[c_2004,c_1826]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_36,negated_conjecture,
% 0.36/1.06      ( ~ v2_struct_0(sK0) ),
% 0.36/1.06      inference(cnf_transformation,[],[f86]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_37,plain,
% 0.36/1.06      ( v2_struct_0(sK0) != iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_35,negated_conjecture,
% 0.36/1.06      ( v2_pre_topc(sK0) ),
% 0.36/1.06      inference(cnf_transformation,[],[f87]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_38,plain,
% 0.36/1.06      ( v2_pre_topc(sK0) = iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_34,negated_conjecture,
% 0.36/1.06      ( l1_pre_topc(sK0) ),
% 0.36/1.06      inference(cnf_transformation,[],[f88]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_39,plain,
% 0.36/1.06      ( l1_pre_topc(sK0) = iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_33,negated_conjecture,
% 0.36/1.06      ( ~ v2_struct_0(sK1) ),
% 0.36/1.06      inference(cnf_transformation,[],[f89]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_40,plain,
% 0.36/1.06      ( v2_struct_0(sK1) != iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_27,negated_conjecture,
% 0.36/1.06      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 0.36/1.06      inference(cnf_transformation,[],[f95]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_46,plain,
% 0.36/1.06      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_2072,plain,
% 0.36/1.06      ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
% 0.36/1.06      | m1_pre_topc(X0,sK1) != iProver_top ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_2005,c_37,c_38,c_39,c_40,c_41,c_42,c_46]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_2080,plain,
% 0.36/1.06      ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_1346,c_2072]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_8,plain,
% 0.36/1.06      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 0.36/1.06      inference(cnf_transformation,[],[f70]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_11,plain,
% 0.36/1.06      ( v2_struct_0(X0)
% 0.36/1.06      | ~ v1_xboole_0(u1_struct_0(X0))
% 0.36/1.06      | ~ l1_struct_0(X0) ),
% 0.36/1.06      inference(cnf_transformation,[],[f73]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_419,plain,
% 0.36/1.06      ( v2_struct_0(X0)
% 0.36/1.06      | ~ v1_xboole_0(u1_struct_0(X0))
% 0.36/1.06      | ~ l1_pre_topc(X0) ),
% 0.36/1.06      inference(resolution,[status(thm)],[c_8,c_11]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_16,plain,
% 0.36/1.06      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 0.36/1.06      | ~ v1_funct_2(X4,X2,X3)
% 0.36/1.06      | ~ v1_funct_2(X4,X0,X1)
% 0.36/1.06      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 0.36/1.06      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.36/1.06      | v1_xboole_0(X1)
% 0.36/1.06      | v1_xboole_0(X3)
% 0.36/1.06      | ~ v1_funct_1(X4) ),
% 0.36/1.06      inference(cnf_transformation,[],[f101]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_24,negated_conjecture,
% 0.36/1.06      ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
% 0.36/1.06      inference(cnf_transformation,[],[f98]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_439,plain,
% 0.36/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 0.36/1.06      | ~ v1_funct_2(X0,X3,X4)
% 0.36/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.36/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 0.36/1.06      | v1_xboole_0(X4)
% 0.36/1.06      | v1_xboole_0(X2)
% 0.36/1.06      | ~ v1_funct_1(X0)
% 0.36/1.06      | k2_tmap_1(sK1,sK0,sK3,sK2) != X0
% 0.36/1.06      | u1_struct_0(sK2) != X1
% 0.36/1.06      | u1_struct_0(sK0) != X2
% 0.36/1.06      | u1_struct_0(sK0) != X4
% 0.36/1.06      | u1_struct_0(sK1) != X3
% 0.36/1.06      | sK3 != X0 ),
% 0.36/1.06      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_440,plain,
% 0.36/1.06      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 0.36/1.06      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 0.36/1.06      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 0.36/1.06      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 0.36/1.06      | v1_xboole_0(u1_struct_0(sK0))
% 0.36/1.06      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 0.36/1.06      | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 0.36/1.06      inference(unflattening,[status(thm)],[c_439]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_472,plain,
% 0.36/1.06      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 0.36/1.06      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 0.36/1.06      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 0.36/1.06      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 0.36/1.06      | v2_struct_0(X0)
% 0.36/1.06      | ~ l1_pre_topc(X0)
% 0.36/1.06      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 0.36/1.06      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 0.36/1.06      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 0.36/1.06      inference(resolution_lifted,[status(thm)],[c_419,c_440]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_562,plain,
% 0.36/1.06      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 0.36/1.06      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 0.36/1.06      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 0.36/1.06      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 0.36/1.06      | v2_struct_0(X0)
% 0.36/1.06      | ~ l1_pre_topc(X0)
% 0.36/1.06      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 0.36/1.06      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 0.36/1.06      inference(resolution_lifted,[status(thm)],[c_28,c_472]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_800,plain,
% 0.36/1.06      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 0.36/1.06      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 0.36/1.06      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 0.36/1.06      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 0.36/1.06      | sP0_iProver_split
% 0.36/1.06      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
% 0.36/1.06      inference(splitting,
% 0.36/1.06                [splitting(split),new_symbols(definition,[])],
% 0.36/1.06                [c_562]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1331,plain,
% 0.36/1.06      ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 0.36/1.06      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 0.36/1.06      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 0.36/1.06      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 0.36/1.06      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 0.36/1.06      | sP0_iProver_split = iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_800]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_2082,plain,
% 0.36/1.06      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 0.36/1.06      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 0.36/1.06      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 0.36/1.06      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 0.36/1.06      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 0.36/1.06      | sP0_iProver_split = iProver_top ),
% 0.36/1.06      inference(demodulation,[status(thm)],[c_2080,c_1331]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_799,plain,
% 0.36/1.06      ( v2_struct_0(X0)
% 0.36/1.06      | ~ l1_pre_topc(X0)
% 0.36/1.06      | u1_struct_0(X0) != u1_struct_0(sK0)
% 0.36/1.06      | ~ sP0_iProver_split ),
% 0.36/1.06      inference(splitting,
% 0.36/1.06                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 0.36/1.06                [c_562]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1332,plain,
% 0.36/1.06      ( u1_struct_0(X0) != u1_struct_0(sK0)
% 0.36/1.06      | v2_struct_0(X0) = iProver_top
% 0.36/1.06      | l1_pre_topc(X0) != iProver_top
% 0.36/1.06      | sP0_iProver_split != iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_799]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1911,plain,
% 0.36/1.06      ( v2_struct_0(sK0) = iProver_top
% 0.36/1.06      | l1_pre_topc(sK0) != iProver_top
% 0.36/1.06      | sP0_iProver_split != iProver_top ),
% 0.36/1.06      inference(equality_resolution,[status(thm)],[c_1332]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_2161,plain,
% 0.36/1.06      ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 0.36/1.06      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 0.36/1.06      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 0.36/1.06      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 0.36/1.06      | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_2082,c_37,c_39,c_1911]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_2162,plain,
% 0.36/1.06      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 0.36/1.06      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 0.36/1.06      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 0.36/1.06      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 0.36/1.06      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 0.36/1.06      inference(renaming,[status(thm)],[c_2161]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_8324,plain,
% 0.36/1.06      ( k7_relat_1(sK3,u1_struct_0(sK1)) != sK3
% 0.36/1.06      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 0.36/1.06      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 0.36/1.06      inference(demodulation,[status(thm)],[c_8315,c_2162]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_5,plain,
% 0.36/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.36/1.06      | v4_relat_1(X0,X1) ),
% 0.36/1.06      inference(cnf_transformation,[],[f67]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_3,plain,
% 0.36/1.06      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 0.36/1.06      inference(cnf_transformation,[],[f65]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_399,plain,
% 0.36/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.36/1.06      | ~ v1_relat_1(X0)
% 0.36/1.06      | k7_relat_1(X0,X1) = X0 ),
% 0.36/1.06      inference(resolution,[status(thm)],[c_5,c_3]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_4,plain,
% 0.36/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.36/1.06      | v1_relat_1(X0) ),
% 0.36/1.06      inference(cnf_transformation,[],[f66]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_403,plain,
% 0.36/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.36/1.06      | k7_relat_1(X0,X1) = X0 ),
% 0.36/1.06      inference(global_propositional_subsumption,
% 0.36/1.06                [status(thm)],
% 0.36/1.06                [c_399,c_5,c_4,c_3]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1335,plain,
% 0.36/1.06      ( k7_relat_1(X0,X1) = X0
% 0.36/1.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_2173,plain,
% 0.36/1.06      ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_1348,c_1335]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_8335,plain,
% 0.36/1.06      ( sK3 != sK3
% 0.36/1.06      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 0.36/1.06      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 0.36/1.06      inference(light_normalisation,[status(thm)],[c_8324,c_2173]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_8336,plain,
% 0.36/1.06      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 0.36/1.06      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 0.36/1.06      inference(equality_resolution_simp,[status(thm)],[c_8335]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_47,plain,
% 0.36/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(contradiction,plain,
% 0.36/1.06      ( $false ),
% 0.36/1.06      inference(minisat,[status(thm)],[c_8336,c_47,c_46]) ).
% 0.36/1.06  
% 0.36/1.06  
% 0.36/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 0.36/1.06  
% 0.36/1.06  ------                               Statistics
% 0.36/1.06  
% 0.36/1.06  ------ General
% 0.36/1.06  
% 0.36/1.06  abstr_ref_over_cycles:                  0
% 0.36/1.06  abstr_ref_under_cycles:                 0
% 0.36/1.06  gc_basic_clause_elim:                   0
% 0.36/1.06  forced_gc_time:                         0
% 0.36/1.06  parsing_time:                           0.012
% 0.36/1.06  unif_index_cands_time:                  0.
% 0.36/1.06  unif_index_add_time:                    0.
% 0.36/1.06  orderings_time:                         0.
% 0.36/1.06  out_proof_time:                         0.013
% 0.36/1.06  total_time:                             0.251
% 0.36/1.06  num_of_symbols:                         57
% 0.36/1.06  num_of_terms:                           4003
% 0.36/1.06  
% 0.36/1.06  ------ Preprocessing
% 0.36/1.06  
% 0.36/1.06  num_of_splits:                          1
% 0.36/1.06  num_of_split_atoms:                     1
% 0.36/1.06  num_of_reused_defs:                     0
% 0.36/1.06  num_eq_ax_congr_red:                    9
% 0.36/1.06  num_of_sem_filtered_clauses:            1
% 0.36/1.06  num_of_subtypes:                        0
% 0.36/1.06  monotx_restored_types:                  0
% 0.36/1.06  sat_num_of_epr_types:                   0
% 0.36/1.06  sat_num_of_non_cyclic_types:            0
% 0.36/1.06  sat_guarded_non_collapsed_types:        0
% 0.36/1.06  num_pure_diseq_elim:                    0
% 0.36/1.06  simp_replaced_by:                       0
% 0.36/1.06  res_preprocessed:                       156
% 0.36/1.06  prep_upred:                             0
% 0.36/1.06  prep_unflattend:                        13
% 0.36/1.06  smt_new_axioms:                         0
% 0.36/1.06  pred_elim_cands:                        7
% 0.36/1.06  pred_elim:                              6
% 0.36/1.06  pred_elim_cl:                           7
% 0.36/1.06  pred_elim_cycles:                       8
% 0.36/1.06  merged_defs:                            0
% 1.53/1.06  merged_defs_ncl:                        0
% 1.53/1.06  bin_hyper_res:                          0
% 1.53/1.06  prep_cycles:                            4
% 1.53/1.06  pred_elim_time:                         0.006
% 1.53/1.06  splitting_time:                         0.
% 1.53/1.06  sem_filter_time:                        0.
% 1.53/1.06  monotx_time:                            0.
% 1.53/1.06  subtype_inf_time:                       0.
% 1.53/1.06  
% 1.53/1.06  ------ Problem properties
% 1.53/1.06  
% 1.53/1.06  clauses:                                29
% 1.53/1.06  conjectures:                            11
% 1.53/1.06  epr:                                    12
% 1.53/1.06  horn:                                   28
% 1.53/1.06  ground:                                 12
% 1.53/1.06  unary:                                  12
% 1.53/1.06  binary:                                 5
% 1.53/1.06  lits:                                   80
% 1.53/1.06  lits_eq:                                7
% 1.53/1.06  fd_pure:                                0
% 1.53/1.06  fd_pseudo:                              0
% 1.53/1.06  fd_cond:                                0
% 1.53/1.06  fd_pseudo_cond:                         1
% 1.53/1.06  ac_symbols:                             0
% 1.53/1.06  
% 1.53/1.06  ------ Propositional Solver
% 1.53/1.06  
% 1.53/1.06  prop_solver_calls:                      30
% 1.53/1.06  prop_fast_solver_calls:                 1406
% 1.53/1.06  smt_solver_calls:                       0
% 1.53/1.06  smt_fast_solver_calls:                  0
% 1.53/1.06  prop_num_of_clauses:                    2257
% 1.53/1.06  prop_preprocess_simplified:             6580
% 1.53/1.06  prop_fo_subsumed:                       78
% 1.53/1.06  prop_solver_time:                       0.
% 1.53/1.06  smt_solver_time:                        0.
% 1.53/1.06  smt_fast_solver_time:                   0.
% 1.53/1.06  prop_fast_solver_time:                  0.
% 1.53/1.06  prop_unsat_core_time:                   0.
% 1.53/1.06  
% 1.53/1.06  ------ QBF
% 1.53/1.06  
% 1.53/1.06  qbf_q_res:                              0
% 1.53/1.06  qbf_num_tautologies:                    0
% 1.53/1.06  qbf_prep_cycles:                        0
% 1.53/1.06  
% 1.53/1.06  ------ BMC1
% 1.53/1.06  
% 1.53/1.06  bmc1_current_bound:                     -1
% 1.53/1.06  bmc1_last_solved_bound:                 -1
% 1.53/1.06  bmc1_unsat_core_size:                   -1
% 1.53/1.06  bmc1_unsat_core_parents_size:           -1
% 1.53/1.06  bmc1_merge_next_fun:                    0
% 1.53/1.06  bmc1_unsat_core_clauses_time:           0.
% 1.53/1.06  
% 1.53/1.06  ------ Instantiation
% 1.53/1.06  
% 1.53/1.06  inst_num_of_clauses:                    640
% 1.53/1.06  inst_num_in_passive:                    56
% 1.53/1.06  inst_num_in_active:                     466
% 1.53/1.06  inst_num_in_unprocessed:                118
% 1.53/1.06  inst_num_of_loops:                      480
% 1.53/1.06  inst_num_of_learning_restarts:          0
% 1.53/1.06  inst_num_moves_active_passive:          8
% 1.53/1.06  inst_lit_activity:                      0
% 1.53/1.06  inst_lit_activity_moves:                0
% 1.53/1.06  inst_num_tautologies:                   0
% 1.53/1.06  inst_num_prop_implied:                  0
% 1.53/1.06  inst_num_existing_simplified:           0
% 1.53/1.06  inst_num_eq_res_simplified:             0
% 1.53/1.06  inst_num_child_elim:                    0
% 1.53/1.06  inst_num_of_dismatching_blockings:      217
% 1.53/1.06  inst_num_of_non_proper_insts:           1089
% 1.53/1.06  inst_num_of_duplicates:                 0
% 1.53/1.06  inst_inst_num_from_inst_to_res:         0
% 1.53/1.06  inst_dismatching_checking_time:         0.
% 1.53/1.06  
% 1.53/1.06  ------ Resolution
% 1.53/1.06  
% 1.53/1.06  res_num_of_clauses:                     0
% 1.53/1.06  res_num_in_passive:                     0
% 1.53/1.06  res_num_in_active:                      0
% 1.53/1.06  res_num_of_loops:                       160
% 1.53/1.06  res_forward_subset_subsumed:            209
% 1.53/1.06  res_backward_subset_subsumed:           0
% 1.53/1.06  res_forward_subsumed:                   0
% 1.53/1.06  res_backward_subsumed:                  0
% 1.53/1.06  res_forward_subsumption_resolution:     0
% 1.53/1.06  res_backward_subsumption_resolution:    0
% 1.53/1.06  res_clause_to_clause_subsumption:       1491
% 1.53/1.06  res_orphan_elimination:                 0
% 1.53/1.06  res_tautology_del:                      124
% 1.53/1.06  res_num_eq_res_simplified:              0
% 1.53/1.06  res_num_sel_changes:                    0
% 1.53/1.06  res_moves_from_active_to_pass:          0
% 1.53/1.06  
% 1.53/1.06  ------ Superposition
% 1.53/1.06  
% 1.53/1.06  sup_time_total:                         0.
% 1.53/1.06  sup_time_generating:                    0.
% 1.53/1.06  sup_time_sim_full:                      0.
% 1.53/1.06  sup_time_sim_immed:                     0.
% 1.53/1.06  
% 1.53/1.06  sup_num_of_clauses:                     188
% 1.53/1.06  sup_num_in_active:                      85
% 1.53/1.06  sup_num_in_passive:                     103
% 1.53/1.06  sup_num_of_loops:                       95
% 1.53/1.06  sup_fw_superposition:                   199
% 1.53/1.06  sup_bw_superposition:                   192
% 1.53/1.06  sup_immediate_simplified:               144
% 1.53/1.06  sup_given_eliminated:                   0
% 1.53/1.06  comparisons_done:                       0
% 1.53/1.06  comparisons_avoided:                    0
% 1.53/1.06  
% 1.53/1.06  ------ Simplifications
% 1.53/1.06  
% 1.53/1.06  
% 1.53/1.06  sim_fw_subset_subsumed:                 87
% 1.53/1.06  sim_bw_subset_subsumed:                 19
% 1.53/1.06  sim_fw_subsumed:                        26
% 1.53/1.06  sim_bw_subsumed:                        12
% 1.53/1.06  sim_fw_subsumption_res:                 3
% 1.53/1.06  sim_bw_subsumption_res:                 0
% 1.53/1.06  sim_tautology_del:                      21
% 1.53/1.06  sim_eq_tautology_del:                   8
% 1.53/1.06  sim_eq_res_simp:                        1
% 1.53/1.06  sim_fw_demodulated:                     1
% 1.53/1.06  sim_bw_demodulated:                     10
% 1.53/1.06  sim_light_normalised:                   22
% 1.53/1.06  sim_joinable_taut:                      0
% 1.53/1.06  sim_joinable_simp:                      0
% 1.53/1.06  sim_ac_normalised:                      0
% 1.53/1.06  sim_smt_subsumption:                    0
% 1.53/1.06  
%------------------------------------------------------------------------------
