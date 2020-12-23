%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:29 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 513 expanded)
%              Number of clauses        :  100 ( 152 expanded)
%              Number of leaves         :   21 ( 159 expanded)
%              Depth                    :   20
%              Number of atoms          :  706 (4398 expanded)
%              Number of equality atoms :  218 ( 609 expanded)
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
    inference(ennf_transformation,[],[f18])).

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
    inference(flattening,[],[f38])).

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f48,f47,f46,f45])).

fof(f78,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f70,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f49])).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f34])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f32])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f86,plain,(
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
    inference(equality_resolution,[],[f67])).

fof(f83,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

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

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1539,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1543,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1547,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2869,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1543,c_1547])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1550,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3426,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2869,c_1550])).

cnf(c_3770,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2869,c_3426])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_69,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5029,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3770,c_69,c_2869,c_3426])).

cnf(c_5030,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5029])).

cnf(c_5035,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_pre_topc(sK1,sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_5030])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_39,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_20,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

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
    inference(cnf_transformation,[],[f64])).

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

cnf(c_1545,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2472,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_1545])).

cnf(c_22,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_13,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1544,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2876,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1544])).

cnf(c_2881,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2876])).

cnf(c_5186,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5035,c_39,c_48,c_63,c_2472,c_2881])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1541,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

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
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_540,plain,
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
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_541,plain,
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
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_1528,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_2133,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1541,c_1528])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_576,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_577,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_1527,plain,
    ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_577])).

cnf(c_2048,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1541,c_1527])).

cnf(c_2134,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2133,c_2048])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_34,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_35,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_36,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_37,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_38,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_43,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2234,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2134,c_34,c_35,c_36,c_37,c_38,c_39,c_43])).

cnf(c_2240,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_1539,c_2234])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_12,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_445,plain,
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
    inference(cnf_transformation,[],[f86])).

cnf(c_21,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_465,plain,
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
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_466,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_498,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_445,c_466])).

cnf(c_588,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_25,c_498])).

cnf(c_868,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | sP0_iProver_split
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_588])).

cnf(c_1525,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_868])).

cnf(c_2309,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2240,c_1525])).

cnf(c_867,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_588])).

cnf(c_1526,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK0)
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_867])).

cnf(c_2130,plain,
    ( v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1526])).

cnf(c_2680,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2309,c_34,c_36,c_2130])).

cnf(c_2681,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2680])).

cnf(c_5192,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5186,c_2681])).

cnf(c_2393,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1541,c_1547])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_244,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_245,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_244])).

cnf(c_313,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_245])).

cnf(c_1530,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_2759,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2393,c_1530])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3148,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3149,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3148])).

cnf(c_3518,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2759,c_3149])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_8,c_7])).

cnf(c_1529,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_2312,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1541,c_1529])).

cnf(c_3522,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
    inference(superposition,[status(thm)],[c_3518,c_2312])).

cnf(c_5196,plain,
    ( sK3 != sK3
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5192,c_3522])).

cnf(c_5197,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5196])).

cnf(c_44,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5197,c_44,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:58:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.58/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.02  
% 3.58/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.58/1.02  
% 3.58/1.02  ------  iProver source info
% 3.58/1.02  
% 3.58/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.58/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.58/1.02  git: non_committed_changes: false
% 3.58/1.02  git: last_make_outside_of_git: false
% 3.58/1.02  
% 3.58/1.02  ------ 
% 3.58/1.02  
% 3.58/1.02  ------ Input Options
% 3.58/1.02  
% 3.58/1.02  --out_options                           all
% 3.58/1.02  --tptp_safe_out                         true
% 3.58/1.02  --problem_path                          ""
% 3.58/1.02  --include_path                          ""
% 3.58/1.02  --clausifier                            res/vclausify_rel
% 3.58/1.02  --clausifier_options                    ""
% 3.58/1.02  --stdin                                 false
% 3.58/1.02  --stats_out                             all
% 3.58/1.02  
% 3.58/1.02  ------ General Options
% 3.58/1.02  
% 3.58/1.02  --fof                                   false
% 3.58/1.02  --time_out_real                         305.
% 3.58/1.02  --time_out_virtual                      -1.
% 3.58/1.02  --symbol_type_check                     false
% 3.58/1.02  --clausify_out                          false
% 3.58/1.02  --sig_cnt_out                           false
% 3.58/1.02  --trig_cnt_out                          false
% 3.58/1.02  --trig_cnt_out_tolerance                1.
% 3.58/1.02  --trig_cnt_out_sk_spl                   false
% 3.58/1.02  --abstr_cl_out                          false
% 3.58/1.02  
% 3.58/1.02  ------ Global Options
% 3.58/1.02  
% 3.58/1.02  --schedule                              default
% 3.58/1.02  --add_important_lit                     false
% 3.58/1.02  --prop_solver_per_cl                    1000
% 3.58/1.02  --min_unsat_core                        false
% 3.58/1.02  --soft_assumptions                      false
% 3.58/1.02  --soft_lemma_size                       3
% 3.58/1.02  --prop_impl_unit_size                   0
% 3.58/1.02  --prop_impl_unit                        []
% 3.58/1.02  --share_sel_clauses                     true
% 3.58/1.02  --reset_solvers                         false
% 3.58/1.02  --bc_imp_inh                            [conj_cone]
% 3.58/1.02  --conj_cone_tolerance                   3.
% 3.58/1.02  --extra_neg_conj                        none
% 3.58/1.02  --large_theory_mode                     true
% 3.58/1.02  --prolific_symb_bound                   200
% 3.58/1.02  --lt_threshold                          2000
% 3.58/1.02  --clause_weak_htbl                      true
% 3.58/1.02  --gc_record_bc_elim                     false
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing Options
% 3.58/1.02  
% 3.58/1.02  --preprocessing_flag                    true
% 3.58/1.02  --time_out_prep_mult                    0.1
% 3.58/1.02  --splitting_mode                        input
% 3.58/1.02  --splitting_grd                         true
% 3.58/1.02  --splitting_cvd                         false
% 3.58/1.02  --splitting_cvd_svl                     false
% 3.58/1.02  --splitting_nvd                         32
% 3.58/1.02  --sub_typing                            true
% 3.58/1.02  --prep_gs_sim                           true
% 3.58/1.02  --prep_unflatten                        true
% 3.58/1.02  --prep_res_sim                          true
% 3.58/1.02  --prep_upred                            true
% 3.58/1.02  --prep_sem_filter                       exhaustive
% 3.58/1.02  --prep_sem_filter_out                   false
% 3.58/1.02  --pred_elim                             true
% 3.58/1.02  --res_sim_input                         true
% 3.58/1.02  --eq_ax_congr_red                       true
% 3.58/1.02  --pure_diseq_elim                       true
% 3.58/1.02  --brand_transform                       false
% 3.58/1.02  --non_eq_to_eq                          false
% 3.58/1.02  --prep_def_merge                        true
% 3.58/1.02  --prep_def_merge_prop_impl              false
% 3.58/1.02  --prep_def_merge_mbd                    true
% 3.58/1.02  --prep_def_merge_tr_red                 false
% 3.58/1.02  --prep_def_merge_tr_cl                  false
% 3.58/1.02  --smt_preprocessing                     true
% 3.58/1.02  --smt_ac_axioms                         fast
% 3.58/1.02  --preprocessed_out                      false
% 3.58/1.02  --preprocessed_stats                    false
% 3.58/1.02  
% 3.58/1.02  ------ Abstraction refinement Options
% 3.58/1.02  
% 3.58/1.02  --abstr_ref                             []
% 3.58/1.02  --abstr_ref_prep                        false
% 3.58/1.02  --abstr_ref_until_sat                   false
% 3.58/1.02  --abstr_ref_sig_restrict                funpre
% 3.58/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.58/1.02  --abstr_ref_under                       []
% 3.58/1.02  
% 3.58/1.02  ------ SAT Options
% 3.58/1.02  
% 3.58/1.02  --sat_mode                              false
% 3.58/1.02  --sat_fm_restart_options                ""
% 3.58/1.02  --sat_gr_def                            false
% 3.58/1.02  --sat_epr_types                         true
% 3.58/1.02  --sat_non_cyclic_types                  false
% 3.58/1.02  --sat_finite_models                     false
% 3.58/1.02  --sat_fm_lemmas                         false
% 3.58/1.02  --sat_fm_prep                           false
% 3.58/1.02  --sat_fm_uc_incr                        true
% 3.58/1.02  --sat_out_model                         small
% 3.58/1.02  --sat_out_clauses                       false
% 3.58/1.02  
% 3.58/1.02  ------ QBF Options
% 3.58/1.02  
% 3.58/1.02  --qbf_mode                              false
% 3.58/1.02  --qbf_elim_univ                         false
% 3.58/1.02  --qbf_dom_inst                          none
% 3.58/1.02  --qbf_dom_pre_inst                      false
% 3.58/1.02  --qbf_sk_in                             false
% 3.58/1.02  --qbf_pred_elim                         true
% 3.58/1.02  --qbf_split                             512
% 3.58/1.02  
% 3.58/1.02  ------ BMC1 Options
% 3.58/1.02  
% 3.58/1.02  --bmc1_incremental                      false
% 3.58/1.02  --bmc1_axioms                           reachable_all
% 3.58/1.02  --bmc1_min_bound                        0
% 3.58/1.02  --bmc1_max_bound                        -1
% 3.58/1.02  --bmc1_max_bound_default                -1
% 3.58/1.02  --bmc1_symbol_reachability              true
% 3.58/1.02  --bmc1_property_lemmas                  false
% 3.58/1.02  --bmc1_k_induction                      false
% 3.58/1.02  --bmc1_non_equiv_states                 false
% 3.58/1.02  --bmc1_deadlock                         false
% 3.58/1.02  --bmc1_ucm                              false
% 3.58/1.02  --bmc1_add_unsat_core                   none
% 3.58/1.02  --bmc1_unsat_core_children              false
% 3.58/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.58/1.02  --bmc1_out_stat                         full
% 3.58/1.02  --bmc1_ground_init                      false
% 3.58/1.02  --bmc1_pre_inst_next_state              false
% 3.58/1.02  --bmc1_pre_inst_state                   false
% 3.58/1.02  --bmc1_pre_inst_reach_state             false
% 3.58/1.02  --bmc1_out_unsat_core                   false
% 3.58/1.02  --bmc1_aig_witness_out                  false
% 3.58/1.02  --bmc1_verbose                          false
% 3.58/1.02  --bmc1_dump_clauses_tptp                false
% 3.58/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.58/1.02  --bmc1_dump_file                        -
% 3.58/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.58/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.58/1.02  --bmc1_ucm_extend_mode                  1
% 3.58/1.02  --bmc1_ucm_init_mode                    2
% 3.58/1.02  --bmc1_ucm_cone_mode                    none
% 3.58/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.58/1.02  --bmc1_ucm_relax_model                  4
% 3.58/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.58/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.58/1.02  --bmc1_ucm_layered_model                none
% 3.58/1.02  --bmc1_ucm_max_lemma_size               10
% 3.58/1.02  
% 3.58/1.02  ------ AIG Options
% 3.58/1.02  
% 3.58/1.02  --aig_mode                              false
% 3.58/1.02  
% 3.58/1.02  ------ Instantiation Options
% 3.58/1.02  
% 3.58/1.02  --instantiation_flag                    true
% 3.58/1.02  --inst_sos_flag                         true
% 3.58/1.02  --inst_sos_phase                        true
% 3.58/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.58/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.58/1.02  --inst_lit_sel_side                     num_symb
% 3.58/1.02  --inst_solver_per_active                1400
% 3.58/1.02  --inst_solver_calls_frac                1.
% 3.58/1.02  --inst_passive_queue_type               priority_queues
% 3.58/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.58/1.02  --inst_passive_queues_freq              [25;2]
% 3.58/1.02  --inst_dismatching                      true
% 3.58/1.02  --inst_eager_unprocessed_to_passive     true
% 3.58/1.02  --inst_prop_sim_given                   true
% 3.58/1.02  --inst_prop_sim_new                     false
% 3.58/1.02  --inst_subs_new                         false
% 3.58/1.02  --inst_eq_res_simp                      false
% 3.58/1.02  --inst_subs_given                       false
% 3.58/1.02  --inst_orphan_elimination               true
% 3.58/1.02  --inst_learning_loop_flag               true
% 3.58/1.02  --inst_learning_start                   3000
% 3.58/1.02  --inst_learning_factor                  2
% 3.58/1.02  --inst_start_prop_sim_after_learn       3
% 3.58/1.02  --inst_sel_renew                        solver
% 3.58/1.02  --inst_lit_activity_flag                true
% 3.58/1.02  --inst_restr_to_given                   false
% 3.58/1.02  --inst_activity_threshold               500
% 3.58/1.02  --inst_out_proof                        true
% 3.58/1.02  
% 3.58/1.02  ------ Resolution Options
% 3.58/1.02  
% 3.58/1.02  --resolution_flag                       true
% 3.58/1.02  --res_lit_sel                           adaptive
% 3.58/1.02  --res_lit_sel_side                      none
% 3.58/1.02  --res_ordering                          kbo
% 3.58/1.02  --res_to_prop_solver                    active
% 3.58/1.02  --res_prop_simpl_new                    false
% 3.58/1.02  --res_prop_simpl_given                  true
% 3.58/1.02  --res_passive_queue_type                priority_queues
% 3.58/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.58/1.02  --res_passive_queues_freq               [15;5]
% 3.58/1.02  --res_forward_subs                      full
% 3.58/1.02  --res_backward_subs                     full
% 3.58/1.02  --res_forward_subs_resolution           true
% 3.58/1.02  --res_backward_subs_resolution          true
% 3.58/1.02  --res_orphan_elimination                true
% 3.58/1.02  --res_time_limit                        2.
% 3.58/1.02  --res_out_proof                         true
% 3.58/1.02  
% 3.58/1.02  ------ Superposition Options
% 3.58/1.02  
% 3.58/1.02  --superposition_flag                    true
% 3.58/1.02  --sup_passive_queue_type                priority_queues
% 3.58/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.58/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.58/1.02  --demod_completeness_check              fast
% 3.58/1.02  --demod_use_ground                      true
% 3.58/1.02  --sup_to_prop_solver                    passive
% 3.58/1.02  --sup_prop_simpl_new                    true
% 3.58/1.02  --sup_prop_simpl_given                  true
% 3.58/1.02  --sup_fun_splitting                     true
% 3.58/1.02  --sup_smt_interval                      50000
% 3.58/1.02  
% 3.58/1.02  ------ Superposition Simplification Setup
% 3.58/1.02  
% 3.58/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.58/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.58/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.58/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.58/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.58/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.58/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.58/1.02  --sup_immed_triv                        [TrivRules]
% 3.58/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/1.02  --sup_immed_bw_main                     []
% 3.58/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.58/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.58/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/1.02  --sup_input_bw                          []
% 3.58/1.02  
% 3.58/1.02  ------ Combination Options
% 3.58/1.02  
% 3.58/1.02  --comb_res_mult                         3
% 3.58/1.02  --comb_sup_mult                         2
% 3.58/1.02  --comb_inst_mult                        10
% 3.58/1.02  
% 3.58/1.02  ------ Debug Options
% 3.58/1.02  
% 3.58/1.02  --dbg_backtrace                         false
% 3.58/1.02  --dbg_dump_prop_clauses                 false
% 3.58/1.02  --dbg_dump_prop_clauses_file            -
% 3.58/1.02  --dbg_out_stat                          false
% 3.58/1.02  ------ Parsing...
% 3.58/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/1.02  ------ Proving...
% 3.58/1.02  ------ Problem Properties 
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  clauses                                 27
% 3.58/1.02  conjectures                             11
% 3.58/1.02  EPR                                     13
% 3.58/1.02  Horn                                    26
% 3.58/1.02  unary                                   13
% 3.58/1.02  binary                                  4
% 3.58/1.02  lits                                    62
% 3.58/1.02  lits eq                                 7
% 3.58/1.02  fd_pure                                 0
% 3.58/1.02  fd_pseudo                               0
% 3.58/1.02  fd_cond                                 0
% 3.58/1.02  fd_pseudo_cond                          1
% 3.58/1.02  AC symbols                              0
% 3.58/1.02  
% 3.58/1.02  ------ Schedule dynamic 5 is on 
% 3.58/1.02  
% 3.58/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  ------ 
% 3.58/1.02  Current options:
% 3.58/1.02  ------ 
% 3.58/1.02  
% 3.58/1.02  ------ Input Options
% 3.58/1.02  
% 3.58/1.02  --out_options                           all
% 3.58/1.02  --tptp_safe_out                         true
% 3.58/1.02  --problem_path                          ""
% 3.58/1.02  --include_path                          ""
% 3.58/1.02  --clausifier                            res/vclausify_rel
% 3.58/1.02  --clausifier_options                    ""
% 3.58/1.02  --stdin                                 false
% 3.58/1.02  --stats_out                             all
% 3.58/1.02  
% 3.58/1.02  ------ General Options
% 3.58/1.02  
% 3.58/1.02  --fof                                   false
% 3.58/1.02  --time_out_real                         305.
% 3.58/1.02  --time_out_virtual                      -1.
% 3.58/1.03  --symbol_type_check                     false
% 3.58/1.03  --clausify_out                          false
% 3.58/1.03  --sig_cnt_out                           false
% 3.58/1.03  --trig_cnt_out                          false
% 3.58/1.03  --trig_cnt_out_tolerance                1.
% 3.58/1.03  --trig_cnt_out_sk_spl                   false
% 3.58/1.03  --abstr_cl_out                          false
% 3.58/1.03  
% 3.58/1.03  ------ Global Options
% 3.58/1.03  
% 3.58/1.03  --schedule                              default
% 3.58/1.03  --add_important_lit                     false
% 3.58/1.03  --prop_solver_per_cl                    1000
% 3.58/1.03  --min_unsat_core                        false
% 3.58/1.03  --soft_assumptions                      false
% 3.58/1.03  --soft_lemma_size                       3
% 3.58/1.03  --prop_impl_unit_size                   0
% 3.58/1.03  --prop_impl_unit                        []
% 3.58/1.03  --share_sel_clauses                     true
% 3.58/1.03  --reset_solvers                         false
% 3.58/1.03  --bc_imp_inh                            [conj_cone]
% 3.58/1.03  --conj_cone_tolerance                   3.
% 3.58/1.03  --extra_neg_conj                        none
% 3.58/1.03  --large_theory_mode                     true
% 3.58/1.03  --prolific_symb_bound                   200
% 3.58/1.03  --lt_threshold                          2000
% 3.58/1.03  --clause_weak_htbl                      true
% 3.58/1.03  --gc_record_bc_elim                     false
% 3.58/1.03  
% 3.58/1.03  ------ Preprocessing Options
% 3.58/1.03  
% 3.58/1.03  --preprocessing_flag                    true
% 3.58/1.03  --time_out_prep_mult                    0.1
% 3.58/1.03  --splitting_mode                        input
% 3.58/1.03  --splitting_grd                         true
% 3.58/1.03  --splitting_cvd                         false
% 3.58/1.03  --splitting_cvd_svl                     false
% 3.58/1.03  --splitting_nvd                         32
% 3.58/1.03  --sub_typing                            true
% 3.58/1.03  --prep_gs_sim                           true
% 3.58/1.03  --prep_unflatten                        true
% 3.58/1.03  --prep_res_sim                          true
% 3.58/1.03  --prep_upred                            true
% 3.58/1.03  --prep_sem_filter                       exhaustive
% 3.58/1.03  --prep_sem_filter_out                   false
% 3.58/1.03  --pred_elim                             true
% 3.58/1.03  --res_sim_input                         true
% 3.58/1.03  --eq_ax_congr_red                       true
% 3.58/1.03  --pure_diseq_elim                       true
% 3.58/1.03  --brand_transform                       false
% 3.58/1.03  --non_eq_to_eq                          false
% 3.58/1.03  --prep_def_merge                        true
% 3.58/1.03  --prep_def_merge_prop_impl              false
% 3.58/1.03  --prep_def_merge_mbd                    true
% 3.58/1.03  --prep_def_merge_tr_red                 false
% 3.58/1.03  --prep_def_merge_tr_cl                  false
% 3.58/1.03  --smt_preprocessing                     true
% 3.58/1.03  --smt_ac_axioms                         fast
% 3.58/1.03  --preprocessed_out                      false
% 3.58/1.03  --preprocessed_stats                    false
% 3.58/1.03  
% 3.58/1.03  ------ Abstraction refinement Options
% 3.58/1.03  
% 3.58/1.03  --abstr_ref                             []
% 3.58/1.03  --abstr_ref_prep                        false
% 3.58/1.03  --abstr_ref_until_sat                   false
% 3.58/1.03  --abstr_ref_sig_restrict                funpre
% 3.58/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.58/1.03  --abstr_ref_under                       []
% 3.58/1.03  
% 3.58/1.03  ------ SAT Options
% 3.58/1.03  
% 3.58/1.03  --sat_mode                              false
% 3.58/1.03  --sat_fm_restart_options                ""
% 3.58/1.03  --sat_gr_def                            false
% 3.58/1.03  --sat_epr_types                         true
% 3.58/1.03  --sat_non_cyclic_types                  false
% 3.58/1.03  --sat_finite_models                     false
% 3.58/1.03  --sat_fm_lemmas                         false
% 3.58/1.03  --sat_fm_prep                           false
% 3.58/1.03  --sat_fm_uc_incr                        true
% 3.58/1.03  --sat_out_model                         small
% 3.58/1.03  --sat_out_clauses                       false
% 3.58/1.03  
% 3.58/1.03  ------ QBF Options
% 3.58/1.03  
% 3.58/1.03  --qbf_mode                              false
% 3.58/1.03  --qbf_elim_univ                         false
% 3.58/1.03  --qbf_dom_inst                          none
% 3.58/1.03  --qbf_dom_pre_inst                      false
% 3.58/1.03  --qbf_sk_in                             false
% 3.58/1.03  --qbf_pred_elim                         true
% 3.58/1.03  --qbf_split                             512
% 3.58/1.03  
% 3.58/1.03  ------ BMC1 Options
% 3.58/1.03  
% 3.58/1.03  --bmc1_incremental                      false
% 3.58/1.03  --bmc1_axioms                           reachable_all
% 3.58/1.03  --bmc1_min_bound                        0
% 3.58/1.03  --bmc1_max_bound                        -1
% 3.58/1.03  --bmc1_max_bound_default                -1
% 3.58/1.03  --bmc1_symbol_reachability              true
% 3.58/1.03  --bmc1_property_lemmas                  false
% 3.58/1.03  --bmc1_k_induction                      false
% 3.58/1.03  --bmc1_non_equiv_states                 false
% 3.58/1.03  --bmc1_deadlock                         false
% 3.58/1.03  --bmc1_ucm                              false
% 3.58/1.03  --bmc1_add_unsat_core                   none
% 3.58/1.03  --bmc1_unsat_core_children              false
% 3.58/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.58/1.03  --bmc1_out_stat                         full
% 3.58/1.03  --bmc1_ground_init                      false
% 3.58/1.03  --bmc1_pre_inst_next_state              false
% 3.58/1.03  --bmc1_pre_inst_state                   false
% 3.58/1.03  --bmc1_pre_inst_reach_state             false
% 3.58/1.03  --bmc1_out_unsat_core                   false
% 3.58/1.03  --bmc1_aig_witness_out                  false
% 3.58/1.03  --bmc1_verbose                          false
% 3.58/1.03  --bmc1_dump_clauses_tptp                false
% 3.58/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.58/1.03  --bmc1_dump_file                        -
% 3.58/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.58/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.58/1.03  --bmc1_ucm_extend_mode                  1
% 3.58/1.03  --bmc1_ucm_init_mode                    2
% 3.58/1.03  --bmc1_ucm_cone_mode                    none
% 3.58/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.58/1.03  --bmc1_ucm_relax_model                  4
% 3.58/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.58/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.58/1.03  --bmc1_ucm_layered_model                none
% 3.58/1.03  --bmc1_ucm_max_lemma_size               10
% 3.58/1.03  
% 3.58/1.03  ------ AIG Options
% 3.58/1.03  
% 3.58/1.03  --aig_mode                              false
% 3.58/1.03  
% 3.58/1.03  ------ Instantiation Options
% 3.58/1.03  
% 3.58/1.03  --instantiation_flag                    true
% 3.58/1.03  --inst_sos_flag                         true
% 3.58/1.03  --inst_sos_phase                        true
% 3.58/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.58/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.58/1.03  --inst_lit_sel_side                     none
% 3.58/1.03  --inst_solver_per_active                1400
% 3.58/1.03  --inst_solver_calls_frac                1.
% 3.58/1.03  --inst_passive_queue_type               priority_queues
% 3.58/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.58/1.03  --inst_passive_queues_freq              [25;2]
% 3.58/1.03  --inst_dismatching                      true
% 3.58/1.03  --inst_eager_unprocessed_to_passive     true
% 3.58/1.03  --inst_prop_sim_given                   true
% 3.58/1.03  --inst_prop_sim_new                     false
% 3.58/1.03  --inst_subs_new                         false
% 3.58/1.03  --inst_eq_res_simp                      false
% 3.58/1.03  --inst_subs_given                       false
% 3.58/1.03  --inst_orphan_elimination               true
% 3.58/1.03  --inst_learning_loop_flag               true
% 3.58/1.03  --inst_learning_start                   3000
% 3.58/1.03  --inst_learning_factor                  2
% 3.58/1.03  --inst_start_prop_sim_after_learn       3
% 3.58/1.03  --inst_sel_renew                        solver
% 3.58/1.03  --inst_lit_activity_flag                true
% 3.58/1.03  --inst_restr_to_given                   false
% 3.58/1.03  --inst_activity_threshold               500
% 3.58/1.03  --inst_out_proof                        true
% 3.58/1.03  
% 3.58/1.03  ------ Resolution Options
% 3.58/1.03  
% 3.58/1.03  --resolution_flag                       false
% 3.58/1.03  --res_lit_sel                           adaptive
% 3.58/1.03  --res_lit_sel_side                      none
% 3.58/1.03  --res_ordering                          kbo
% 3.58/1.03  --res_to_prop_solver                    active
% 3.58/1.03  --res_prop_simpl_new                    false
% 3.58/1.03  --res_prop_simpl_given                  true
% 3.58/1.03  --res_passive_queue_type                priority_queues
% 3.58/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.58/1.03  --res_passive_queues_freq               [15;5]
% 3.58/1.03  --res_forward_subs                      full
% 3.58/1.03  --res_backward_subs                     full
% 3.58/1.03  --res_forward_subs_resolution           true
% 3.58/1.03  --res_backward_subs_resolution          true
% 3.58/1.03  --res_orphan_elimination                true
% 3.58/1.03  --res_time_limit                        2.
% 3.58/1.03  --res_out_proof                         true
% 3.58/1.03  
% 3.58/1.03  ------ Superposition Options
% 3.58/1.03  
% 3.58/1.03  --superposition_flag                    true
% 3.58/1.03  --sup_passive_queue_type                priority_queues
% 3.58/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.58/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.58/1.03  --demod_completeness_check              fast
% 3.58/1.03  --demod_use_ground                      true
% 3.58/1.03  --sup_to_prop_solver                    passive
% 3.58/1.03  --sup_prop_simpl_new                    true
% 3.58/1.03  --sup_prop_simpl_given                  true
% 3.58/1.03  --sup_fun_splitting                     true
% 3.58/1.03  --sup_smt_interval                      50000
% 3.58/1.03  
% 3.58/1.03  ------ Superposition Simplification Setup
% 3.58/1.03  
% 3.58/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.58/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.58/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.58/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.58/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.58/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.58/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.58/1.03  --sup_immed_triv                        [TrivRules]
% 3.58/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/1.03  --sup_immed_bw_main                     []
% 3.58/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.58/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.58/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/1.03  --sup_input_bw                          []
% 3.58/1.03  
% 3.58/1.03  ------ Combination Options
% 3.58/1.03  
% 3.58/1.03  --comb_res_mult                         3
% 3.58/1.03  --comb_sup_mult                         2
% 3.58/1.03  --comb_inst_mult                        10
% 3.58/1.03  
% 3.58/1.03  ------ Debug Options
% 3.58/1.03  
% 3.58/1.03  --dbg_backtrace                         false
% 3.58/1.03  --dbg_dump_prop_clauses                 false
% 3.58/1.03  --dbg_dump_prop_clauses_file            -
% 3.58/1.03  --dbg_out_stat                          false
% 3.58/1.03  
% 3.58/1.03  
% 3.58/1.03  
% 3.58/1.03  
% 3.58/1.03  ------ Proving...
% 3.58/1.03  
% 3.58/1.03  
% 3.58/1.03  % SZS status Theorem for theBenchmark.p
% 3.58/1.03  
% 3.58/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.58/1.03  
% 3.58/1.03  fof(f17,conjecture,(
% 3.58/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 3.58/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/1.03  
% 3.58/1.03  fof(f18,negated_conjecture,(
% 3.58/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 3.58/1.03    inference(negated_conjecture,[],[f17])).
% 3.58/1.03  
% 3.58/1.03  fof(f38,plain,(
% 3.58/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.58/1.03    inference(ennf_transformation,[],[f18])).
% 3.58/1.03  
% 3.58/1.03  fof(f39,plain,(
% 3.58/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.58/1.03    inference(flattening,[],[f38])).
% 3.58/1.03  
% 3.58/1.03  fof(f48,plain,(
% 3.58/1.03    ( ! [X2,X0,X1] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 3.58/1.03    introduced(choice_axiom,[])).
% 3.58/1.03  
% 3.58/1.03  fof(f47,plain,(
% 3.58/1.03    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 3.58/1.03    introduced(choice_axiom,[])).
% 3.58/1.03  
% 3.58/1.03  fof(f46,plain,(
% 3.58/1.03    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.58/1.03    introduced(choice_axiom,[])).
% 3.58/1.03  
% 3.58/1.03  fof(f45,plain,(
% 3.58/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.58/1.03    introduced(choice_axiom,[])).
% 3.58/1.03  
% 3.58/1.03  fof(f49,plain,(
% 3.58/1.03    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.58/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f48,f47,f46,f45])).
% 3.58/1.03  
% 3.58/1.03  fof(f78,plain,(
% 3.58/1.03    m1_pre_topc(sK2,sK1)),
% 3.58/1.03    inference(cnf_transformation,[],[f49])).
% 3.58/1.03  
% 3.58/1.03  fof(f15,axiom,(
% 3.58/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.58/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/1.03  
% 3.58/1.03  fof(f36,plain,(
% 3.58/1.03    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.58/1.03    inference(ennf_transformation,[],[f15])).
% 3.58/1.03  
% 3.58/1.03  fof(f69,plain,(
% 3.58/1.03    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.58/1.03    inference(cnf_transformation,[],[f36])).
% 3.58/1.03  
% 3.58/1.03  fof(f2,axiom,(
% 3.58/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.58/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/1.03  
% 3.58/1.03  fof(f42,plain,(
% 3.58/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.58/1.03    inference(nnf_transformation,[],[f2])).
% 3.58/1.03  
% 3.58/1.03  fof(f53,plain,(
% 3.58/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.58/1.03    inference(cnf_transformation,[],[f42])).
% 3.58/1.03  
% 3.58/1.03  fof(f1,axiom,(
% 3.58/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.58/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/1.03  
% 3.58/1.03  fof(f40,plain,(
% 3.58/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.58/1.03    inference(nnf_transformation,[],[f1])).
% 3.58/1.03  
% 3.58/1.03  fof(f41,plain,(
% 3.58/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.58/1.03    inference(flattening,[],[f40])).
% 3.58/1.03  
% 3.58/1.03  fof(f52,plain,(
% 3.58/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.58/1.03    inference(cnf_transformation,[],[f41])).
% 3.58/1.03  
% 3.58/1.03  fof(f9,axiom,(
% 3.58/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.58/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/1.03  
% 3.58/1.03  fof(f27,plain,(
% 3.58/1.03    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.58/1.03    inference(ennf_transformation,[],[f9])).
% 3.58/1.03  
% 3.58/1.03  fof(f61,plain,(
% 3.58/1.03    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.58/1.03    inference(cnf_transformation,[],[f27])).
% 3.58/1.03  
% 3.58/1.03  fof(f76,plain,(
% 3.58/1.03    l1_pre_topc(sK1)),
% 3.58/1.03    inference(cnf_transformation,[],[f49])).
% 3.58/1.03  
% 3.58/1.03  fof(f16,axiom,(
% 3.58/1.03    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.58/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/1.03  
% 3.58/1.03  fof(f37,plain,(
% 3.58/1.03    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.58/1.03    inference(ennf_transformation,[],[f16])).
% 3.58/1.03  
% 3.58/1.03  fof(f70,plain,(
% 3.58/1.03    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.58/1.03    inference(cnf_transformation,[],[f37])).
% 3.58/1.03  
% 3.58/1.03  fof(f12,axiom,(
% 3.58/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.58/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/1.03  
% 3.58/1.03  fof(f31,plain,(
% 3.58/1.03    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.58/1.03    inference(ennf_transformation,[],[f12])).
% 3.58/1.03  
% 3.58/1.03  fof(f43,plain,(
% 3.58/1.03    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.58/1.03    inference(nnf_transformation,[],[f31])).
% 3.58/1.03  
% 3.58/1.03  fof(f64,plain,(
% 3.58/1.03    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.58/1.03    inference(cnf_transformation,[],[f43])).
% 3.58/1.03  
% 3.58/1.03  fof(f82,plain,(
% 3.58/1.03    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 3.58/1.03    inference(cnf_transformation,[],[f49])).
% 3.58/1.03  
% 3.58/1.03  fof(f11,axiom,(
% 3.58/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.58/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/1.03  
% 3.58/1.03  fof(f30,plain,(
% 3.58/1.03    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.58/1.03    inference(ennf_transformation,[],[f11])).
% 3.58/1.03  
% 3.58/1.03  fof(f63,plain,(
% 3.58/1.03    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.58/1.03    inference(cnf_transformation,[],[f30])).
% 3.58/1.03  
% 3.58/1.03  fof(f81,plain,(
% 3.58/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 3.58/1.03    inference(cnf_transformation,[],[f49])).
% 3.58/1.03  
% 3.58/1.03  fof(f14,axiom,(
% 3.58/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 3.58/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/1.03  
% 3.58/1.03  fof(f34,plain,(
% 3.58/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.58/1.03    inference(ennf_transformation,[],[f14])).
% 3.58/1.03  
% 3.58/1.03  fof(f35,plain,(
% 3.58/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.58/1.03    inference(flattening,[],[f34])).
% 3.58/1.03  
% 3.58/1.03  fof(f68,plain,(
% 3.58/1.03    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/1.03    inference(cnf_transformation,[],[f35])).
% 3.58/1.03  
% 3.58/1.03  fof(f79,plain,(
% 3.58/1.03    v1_funct_1(sK3)),
% 3.58/1.03    inference(cnf_transformation,[],[f49])).
% 3.58/1.03  
% 3.58/1.03  fof(f7,axiom,(
% 3.58/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.58/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/1.03  
% 3.58/1.03  fof(f24,plain,(
% 3.58/1.03    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.58/1.03    inference(ennf_transformation,[],[f7])).
% 3.58/1.03  
% 3.58/1.03  fof(f25,plain,(
% 3.58/1.03    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.58/1.03    inference(flattening,[],[f24])).
% 3.58/1.03  
% 3.58/1.03  fof(f59,plain,(
% 3.58/1.03    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.58/1.03    inference(cnf_transformation,[],[f25])).
% 3.58/1.03  
% 3.58/1.03  fof(f71,plain,(
% 3.58/1.03    ~v2_struct_0(sK0)),
% 3.58/1.03    inference(cnf_transformation,[],[f49])).
% 3.58/1.03  
% 3.58/1.03  fof(f72,plain,(
% 3.58/1.03    v2_pre_topc(sK0)),
% 3.58/1.03    inference(cnf_transformation,[],[f49])).
% 3.58/1.03  
% 3.58/1.03  fof(f73,plain,(
% 3.58/1.03    l1_pre_topc(sK0)),
% 3.58/1.03    inference(cnf_transformation,[],[f49])).
% 3.58/1.03  
% 3.58/1.03  fof(f74,plain,(
% 3.58/1.03    ~v2_struct_0(sK1)),
% 3.58/1.03    inference(cnf_transformation,[],[f49])).
% 3.58/1.03  
% 3.58/1.03  fof(f75,plain,(
% 3.58/1.03    v2_pre_topc(sK1)),
% 3.58/1.03    inference(cnf_transformation,[],[f49])).
% 3.58/1.03  
% 3.58/1.03  fof(f80,plain,(
% 3.58/1.03    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 3.58/1.03    inference(cnf_transformation,[],[f49])).
% 3.58/1.03  
% 3.58/1.03  fof(f8,axiom,(
% 3.58/1.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.58/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/1.03  
% 3.58/1.03  fof(f26,plain,(
% 3.58/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.58/1.03    inference(ennf_transformation,[],[f8])).
% 3.58/1.03  
% 3.58/1.03  fof(f60,plain,(
% 3.58/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.58/1.03    inference(cnf_transformation,[],[f26])).
% 3.58/1.03  
% 3.58/1.03  fof(f10,axiom,(
% 3.58/1.03    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.58/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/1.03  
% 3.58/1.03  fof(f28,plain,(
% 3.58/1.03    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.58/1.03    inference(ennf_transformation,[],[f10])).
% 3.58/1.03  
% 3.58/1.03  fof(f29,plain,(
% 3.58/1.03    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.58/1.03    inference(flattening,[],[f28])).
% 3.58/1.03  
% 3.58/1.03  fof(f62,plain,(
% 3.58/1.03    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.58/1.03    inference(cnf_transformation,[],[f29])).
% 3.58/1.03  
% 3.58/1.03  fof(f13,axiom,(
% 3.58/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.58/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/1.03  
% 3.58/1.03  fof(f32,plain,(
% 3.58/1.03    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.58/1.03    inference(ennf_transformation,[],[f13])).
% 3.58/1.03  
% 3.58/1.03  fof(f33,plain,(
% 3.58/1.03    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.58/1.03    inference(flattening,[],[f32])).
% 3.58/1.03  
% 3.58/1.03  fof(f44,plain,(
% 3.58/1.03    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.58/1.03    inference(nnf_transformation,[],[f33])).
% 3.58/1.03  
% 3.58/1.03  fof(f67,plain,(
% 3.58/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.58/1.03    inference(cnf_transformation,[],[f44])).
% 3.58/1.03  
% 3.58/1.03  fof(f86,plain,(
% 3.58/1.03    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.58/1.03    inference(equality_resolution,[],[f67])).
% 3.58/1.03  
% 3.58/1.03  fof(f83,plain,(
% 3.58/1.03    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 3.58/1.03    inference(cnf_transformation,[],[f49])).
% 3.58/1.03  
% 3.58/1.03  fof(f3,axiom,(
% 3.58/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.58/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/1.03  
% 3.58/1.03  fof(f20,plain,(
% 3.58/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.58/1.03    inference(ennf_transformation,[],[f3])).
% 3.58/1.03  
% 3.58/1.03  fof(f55,plain,(
% 3.58/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.58/1.03    inference(cnf_transformation,[],[f20])).
% 3.58/1.03  
% 3.58/1.03  fof(f54,plain,(
% 3.58/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.58/1.03    inference(cnf_transformation,[],[f42])).
% 3.58/1.03  
% 3.58/1.03  fof(f4,axiom,(
% 3.58/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.58/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/1.03  
% 3.58/1.03  fof(f56,plain,(
% 3.58/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.58/1.03    inference(cnf_transformation,[],[f4])).
% 3.58/1.03  
% 3.58/1.03  fof(f6,axiom,(
% 3.58/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.58/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/1.03  
% 3.58/1.03  fof(f19,plain,(
% 3.58/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.58/1.03    inference(pure_predicate_removal,[],[f6])).
% 3.58/1.03  
% 3.58/1.03  fof(f23,plain,(
% 3.58/1.03    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.58/1.03    inference(ennf_transformation,[],[f19])).
% 3.58/1.03  
% 3.58/1.03  fof(f58,plain,(
% 3.58/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.58/1.03    inference(cnf_transformation,[],[f23])).
% 3.58/1.03  
% 3.58/1.03  fof(f5,axiom,(
% 3.58/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.58/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/1.03  
% 3.58/1.03  fof(f21,plain,(
% 3.58/1.03    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.58/1.03    inference(ennf_transformation,[],[f5])).
% 3.58/1.03  
% 3.58/1.03  fof(f22,plain,(
% 3.58/1.03    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.58/1.03    inference(flattening,[],[f21])).
% 3.58/1.03  
% 3.58/1.03  fof(f57,plain,(
% 3.58/1.03    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.58/1.03    inference(cnf_transformation,[],[f22])).
% 3.58/1.03  
% 3.58/1.03  cnf(c_26,negated_conjecture,
% 3.58/1.03      ( m1_pre_topc(sK2,sK1) ),
% 3.58/1.03      inference(cnf_transformation,[],[f78]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_1539,plain,
% 3.58/1.03      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_19,plain,
% 3.58/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.58/1.03      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.58/1.03      | ~ l1_pre_topc(X1) ),
% 3.58/1.03      inference(cnf_transformation,[],[f69]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_1543,plain,
% 3.58/1.03      ( m1_pre_topc(X0,X1) != iProver_top
% 3.58/1.03      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.58/1.03      | l1_pre_topc(X1) != iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_4,plain,
% 3.58/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.58/1.03      inference(cnf_transformation,[],[f53]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_1547,plain,
% 3.58/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.58/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_2869,plain,
% 3.58/1.03      ( m1_pre_topc(X0,X1) != iProver_top
% 3.58/1.03      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.58/1.03      | l1_pre_topc(X1) != iProver_top ),
% 3.58/1.03      inference(superposition,[status(thm)],[c_1543,c_1547]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_0,plain,
% 3.58/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.58/1.03      inference(cnf_transformation,[],[f52]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_1550,plain,
% 3.58/1.03      ( X0 = X1
% 3.58/1.03      | r1_tarski(X0,X1) != iProver_top
% 3.58/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_3426,plain,
% 3.58/1.03      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.58/1.03      | m1_pre_topc(X1,X0) != iProver_top
% 3.58/1.03      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.58/1.03      | l1_pre_topc(X0) != iProver_top ),
% 3.58/1.03      inference(superposition,[status(thm)],[c_2869,c_1550]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_3770,plain,
% 3.58/1.03      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.58/1.03      | m1_pre_topc(X1,X0) != iProver_top
% 3.58/1.03      | m1_pre_topc(X0,X1) != iProver_top
% 3.58/1.03      | l1_pre_topc(X1) != iProver_top
% 3.58/1.03      | l1_pre_topc(X0) != iProver_top ),
% 3.58/1.03      inference(superposition,[status(thm)],[c_2869,c_3426]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_11,plain,
% 3.58/1.03      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.58/1.03      inference(cnf_transformation,[],[f61]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_69,plain,
% 3.58/1.03      ( m1_pre_topc(X0,X1) != iProver_top
% 3.58/1.03      | l1_pre_topc(X1) != iProver_top
% 3.58/1.03      | l1_pre_topc(X0) = iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_5029,plain,
% 3.58/1.03      ( l1_pre_topc(X1) != iProver_top
% 3.58/1.03      | m1_pre_topc(X0,X1) != iProver_top
% 3.58/1.03      | m1_pre_topc(X1,X0) != iProver_top
% 3.58/1.03      | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.58/1.03      inference(global_propositional_subsumption,
% 3.58/1.03                [status(thm)],
% 3.58/1.03                [c_3770,c_69,c_2869,c_3426]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_5030,plain,
% 3.58/1.03      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.58/1.03      | m1_pre_topc(X0,X1) != iProver_top
% 3.58/1.03      | m1_pre_topc(X1,X0) != iProver_top
% 3.58/1.03      | l1_pre_topc(X1) != iProver_top ),
% 3.58/1.03      inference(renaming,[status(thm)],[c_5029]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_5035,plain,
% 3.58/1.03      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 3.58/1.03      | m1_pre_topc(sK1,sK2) != iProver_top
% 3.58/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 3.58/1.03      inference(superposition,[status(thm)],[c_1539,c_5030]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_28,negated_conjecture,
% 3.58/1.03      ( l1_pre_topc(sK1) ),
% 3.58/1.03      inference(cnf_transformation,[],[f76]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_39,plain,
% 3.58/1.03      ( l1_pre_topc(sK1) = iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_20,plain,
% 3.58/1.03      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.58/1.03      inference(cnf_transformation,[],[f70]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_46,plain,
% 3.58/1.03      ( m1_pre_topc(X0,X0) = iProver_top
% 3.58/1.03      | l1_pre_topc(X0) != iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_48,plain,
% 3.58/1.03      ( m1_pre_topc(sK1,sK1) = iProver_top
% 3.58/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 3.58/1.03      inference(instantiation,[status(thm)],[c_46]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_15,plain,
% 3.58/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.58/1.03      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.58/1.03      | ~ l1_pre_topc(X0)
% 3.58/1.03      | ~ l1_pre_topc(X1) ),
% 3.58/1.03      inference(cnf_transformation,[],[f64]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_61,plain,
% 3.58/1.03      ( m1_pre_topc(X0,X1) != iProver_top
% 3.58/1.03      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.58/1.03      | l1_pre_topc(X0) != iProver_top
% 3.58/1.03      | l1_pre_topc(X1) != iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_63,plain,
% 3.58/1.03      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.58/1.03      | m1_pre_topc(sK1,sK1) != iProver_top
% 3.58/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 3.58/1.03      inference(instantiation,[status(thm)],[c_61]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_1545,plain,
% 3.58/1.03      ( m1_pre_topc(X0,X1) != iProver_top
% 3.58/1.03      | l1_pre_topc(X1) != iProver_top
% 3.58/1.03      | l1_pre_topc(X0) = iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_2472,plain,
% 3.58/1.03      ( l1_pre_topc(sK2) = iProver_top
% 3.58/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 3.58/1.03      inference(superposition,[status(thm)],[c_1539,c_1545]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_22,negated_conjecture,
% 3.58/1.03      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.58/1.03      inference(cnf_transformation,[],[f82]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_13,plain,
% 3.58/1.03      ( m1_pre_topc(X0,X1)
% 3.58/1.03      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.58/1.03      | ~ l1_pre_topc(X1) ),
% 3.58/1.03      inference(cnf_transformation,[],[f63]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_1544,plain,
% 3.58/1.03      ( m1_pre_topc(X0,X1) = iProver_top
% 3.58/1.03      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.58/1.03      | l1_pre_topc(X1) != iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_2876,plain,
% 3.58/1.03      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.58/1.03      | m1_pre_topc(X0,sK2) = iProver_top
% 3.58/1.03      | l1_pre_topc(sK2) != iProver_top ),
% 3.58/1.03      inference(superposition,[status(thm)],[c_22,c_1544]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_2881,plain,
% 3.58/1.03      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.58/1.03      | m1_pre_topc(sK1,sK2) = iProver_top
% 3.58/1.03      | l1_pre_topc(sK2) != iProver_top ),
% 3.58/1.03      inference(instantiation,[status(thm)],[c_2876]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_5186,plain,
% 3.58/1.03      ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 3.58/1.03      inference(global_propositional_subsumption,
% 3.58/1.03                [status(thm)],
% 3.58/1.03                [c_5035,c_39,c_48,c_63,c_2472,c_2881]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_23,negated_conjecture,
% 3.58/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 3.58/1.03      inference(cnf_transformation,[],[f81]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_1541,plain,
% 3.58/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_18,plain,
% 3.58/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.58/1.03      | ~ m1_pre_topc(X3,X1)
% 3.58/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.58/1.03      | ~ v2_pre_topc(X2)
% 3.58/1.03      | ~ v2_pre_topc(X1)
% 3.58/1.03      | v2_struct_0(X1)
% 3.58/1.03      | v2_struct_0(X2)
% 3.58/1.03      | ~ l1_pre_topc(X1)
% 3.58/1.03      | ~ l1_pre_topc(X2)
% 3.58/1.03      | ~ v1_funct_1(X0)
% 3.58/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.58/1.03      inference(cnf_transformation,[],[f68]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_25,negated_conjecture,
% 3.58/1.03      ( v1_funct_1(sK3) ),
% 3.58/1.03      inference(cnf_transformation,[],[f79]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_540,plain,
% 3.58/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.58/1.03      | ~ m1_pre_topc(X3,X1)
% 3.58/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.58/1.03      | ~ v2_pre_topc(X1)
% 3.58/1.03      | ~ v2_pre_topc(X2)
% 3.58/1.03      | v2_struct_0(X1)
% 3.58/1.03      | v2_struct_0(X2)
% 3.58/1.03      | ~ l1_pre_topc(X1)
% 3.58/1.03      | ~ l1_pre_topc(X2)
% 3.58/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 3.58/1.03      | sK3 != X0 ),
% 3.58/1.03      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_541,plain,
% 3.58/1.03      ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
% 3.58/1.03      | ~ m1_pre_topc(X2,X0)
% 3.58/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.58/1.03      | ~ v2_pre_topc(X0)
% 3.58/1.03      | ~ v2_pre_topc(X1)
% 3.58/1.03      | v2_struct_0(X0)
% 3.58/1.03      | v2_struct_0(X1)
% 3.58/1.03      | ~ l1_pre_topc(X0)
% 3.58/1.03      | ~ l1_pre_topc(X1)
% 3.58/1.03      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2) ),
% 3.58/1.03      inference(unflattening,[status(thm)],[c_540]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_1528,plain,
% 3.58/1.03      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2)
% 3.58/1.03      | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.58/1.03      | m1_pre_topc(X2,X0) != iProver_top
% 3.58/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.58/1.03      | v2_pre_topc(X1) != iProver_top
% 3.58/1.03      | v2_pre_topc(X0) != iProver_top
% 3.58/1.03      | v2_struct_0(X1) = iProver_top
% 3.58/1.03      | v2_struct_0(X0) = iProver_top
% 3.58/1.03      | l1_pre_topc(X0) != iProver_top
% 3.58/1.03      | l1_pre_topc(X1) != iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_541]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_2133,plain,
% 3.58/1.03      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 3.58/1.03      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.58/1.03      | m1_pre_topc(X0,sK1) != iProver_top
% 3.58/1.03      | v2_pre_topc(sK0) != iProver_top
% 3.58/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.58/1.03      | v2_struct_0(sK0) = iProver_top
% 3.58/1.03      | v2_struct_0(sK1) = iProver_top
% 3.58/1.03      | l1_pre_topc(sK0) != iProver_top
% 3.58/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 3.58/1.03      inference(superposition,[status(thm)],[c_1541,c_1528]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_9,plain,
% 3.58/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.58/1.03      | ~ v1_funct_1(X0)
% 3.58/1.03      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.58/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_576,plain,
% 3.58/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.58/1.03      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 3.58/1.03      | sK3 != X0 ),
% 3.58/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_577,plain,
% 3.58/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.58/1.03      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.58/1.03      inference(unflattening,[status(thm)],[c_576]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_1527,plain,
% 3.58/1.03      ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 3.58/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_577]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_2048,plain,
% 3.58/1.03      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.58/1.03      inference(superposition,[status(thm)],[c_1541,c_1527]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_2134,plain,
% 3.58/1.03      ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
% 3.58/1.03      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.58/1.03      | m1_pre_topc(X0,sK1) != iProver_top
% 3.58/1.03      | v2_pre_topc(sK0) != iProver_top
% 3.58/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.58/1.03      | v2_struct_0(sK0) = iProver_top
% 3.58/1.03      | v2_struct_0(sK1) = iProver_top
% 3.58/1.03      | l1_pre_topc(sK0) != iProver_top
% 3.58/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 3.58/1.03      inference(demodulation,[status(thm)],[c_2133,c_2048]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_33,negated_conjecture,
% 3.58/1.03      ( ~ v2_struct_0(sK0) ),
% 3.58/1.03      inference(cnf_transformation,[],[f71]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_34,plain,
% 3.58/1.03      ( v2_struct_0(sK0) != iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_32,negated_conjecture,
% 3.58/1.03      ( v2_pre_topc(sK0) ),
% 3.58/1.03      inference(cnf_transformation,[],[f72]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_35,plain,
% 3.58/1.03      ( v2_pre_topc(sK0) = iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_31,negated_conjecture,
% 3.58/1.03      ( l1_pre_topc(sK0) ),
% 3.58/1.03      inference(cnf_transformation,[],[f73]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_36,plain,
% 3.58/1.03      ( l1_pre_topc(sK0) = iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_30,negated_conjecture,
% 3.58/1.03      ( ~ v2_struct_0(sK1) ),
% 3.58/1.03      inference(cnf_transformation,[],[f74]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_37,plain,
% 3.58/1.03      ( v2_struct_0(sK1) != iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_29,negated_conjecture,
% 3.58/1.03      ( v2_pre_topc(sK1) ),
% 3.58/1.03      inference(cnf_transformation,[],[f75]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_38,plain,
% 3.58/1.03      ( v2_pre_topc(sK1) = iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_24,negated_conjecture,
% 3.58/1.03      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 3.58/1.03      inference(cnf_transformation,[],[f80]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_43,plain,
% 3.58/1.03      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_2234,plain,
% 3.58/1.03      ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
% 3.58/1.03      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.58/1.03      inference(global_propositional_subsumption,
% 3.58/1.03                [status(thm)],
% 3.58/1.03                [c_2134,c_34,c_35,c_36,c_37,c_38,c_39,c_43]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_2240,plain,
% 3.58/1.03      ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 3.58/1.03      inference(superposition,[status(thm)],[c_1539,c_2234]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_10,plain,
% 3.58/1.03      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.58/1.03      inference(cnf_transformation,[],[f60]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_12,plain,
% 3.58/1.03      ( v2_struct_0(X0)
% 3.58/1.03      | ~ v1_xboole_0(u1_struct_0(X0))
% 3.58/1.03      | ~ l1_struct_0(X0) ),
% 3.58/1.03      inference(cnf_transformation,[],[f62]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_445,plain,
% 3.58/1.03      ( v2_struct_0(X0)
% 3.58/1.03      | ~ v1_xboole_0(u1_struct_0(X0))
% 3.58/1.03      | ~ l1_pre_topc(X0) ),
% 3.58/1.03      inference(resolution,[status(thm)],[c_10,c_12]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_16,plain,
% 3.58/1.03      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 3.58/1.03      | ~ v1_funct_2(X4,X2,X3)
% 3.58/1.03      | ~ v1_funct_2(X4,X0,X1)
% 3.58/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.58/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.58/1.03      | v1_xboole_0(X1)
% 3.58/1.03      | v1_xboole_0(X3)
% 3.58/1.03      | ~ v1_funct_1(X4) ),
% 3.58/1.03      inference(cnf_transformation,[],[f86]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_21,negated_conjecture,
% 3.58/1.03      ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
% 3.58/1.03      inference(cnf_transformation,[],[f83]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_465,plain,
% 3.58/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.58/1.03      | ~ v1_funct_2(X0,X3,X4)
% 3.58/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.58/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.58/1.03      | v1_xboole_0(X4)
% 3.58/1.03      | v1_xboole_0(X2)
% 3.58/1.03      | ~ v1_funct_1(X0)
% 3.58/1.03      | k2_tmap_1(sK1,sK0,sK3,sK2) != X0
% 3.58/1.03      | u1_struct_0(sK2) != X1
% 3.58/1.03      | u1_struct_0(sK0) != X2
% 3.58/1.03      | u1_struct_0(sK0) != X4
% 3.58/1.03      | u1_struct_0(sK1) != X3
% 3.58/1.03      | sK3 != X0 ),
% 3.58/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_466,plain,
% 3.58/1.03      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 3.58/1.03      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.58/1.03      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 3.58/1.03      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.58/1.03      | v1_xboole_0(u1_struct_0(sK0))
% 3.58/1.03      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 3.58/1.03      | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 3.58/1.03      inference(unflattening,[status(thm)],[c_465]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_498,plain,
% 3.58/1.03      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 3.58/1.03      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.58/1.03      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 3.58/1.03      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.58/1.03      | v2_struct_0(X0)
% 3.58/1.03      | ~ l1_pre_topc(X0)
% 3.58/1.03      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 3.58/1.03      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 3.58/1.03      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 3.58/1.03      inference(resolution_lifted,[status(thm)],[c_445,c_466]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_588,plain,
% 3.58/1.03      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 3.58/1.03      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.58/1.03      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 3.58/1.03      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.58/1.03      | v2_struct_0(X0)
% 3.58/1.03      | ~ l1_pre_topc(X0)
% 3.58/1.03      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 3.58/1.03      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 3.58/1.03      inference(resolution_lifted,[status(thm)],[c_25,c_498]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_868,plain,
% 3.58/1.03      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 3.58/1.03      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.58/1.03      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 3.58/1.03      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.58/1.03      | sP0_iProver_split
% 3.58/1.03      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
% 3.58/1.03      inference(splitting,
% 3.58/1.03                [splitting(split),new_symbols(definition,[])],
% 3.58/1.03                [c_588]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_1525,plain,
% 3.58/1.03      ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 3.58/1.03      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.58/1.03      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.58/1.03      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.58/1.03      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.58/1.03      | sP0_iProver_split = iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_868]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_2309,plain,
% 3.58/1.03      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 3.58/1.03      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.58/1.03      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.58/1.03      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.58/1.03      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.58/1.03      | sP0_iProver_split = iProver_top ),
% 3.58/1.03      inference(demodulation,[status(thm)],[c_2240,c_1525]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_867,plain,
% 3.58/1.03      ( v2_struct_0(X0)
% 3.58/1.03      | ~ l1_pre_topc(X0)
% 3.58/1.03      | u1_struct_0(X0) != u1_struct_0(sK0)
% 3.58/1.03      | ~ sP0_iProver_split ),
% 3.58/1.03      inference(splitting,
% 3.58/1.03                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.58/1.03                [c_588]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_1526,plain,
% 3.58/1.03      ( u1_struct_0(X0) != u1_struct_0(sK0)
% 3.58/1.03      | v2_struct_0(X0) = iProver_top
% 3.58/1.03      | l1_pre_topc(X0) != iProver_top
% 3.58/1.03      | sP0_iProver_split != iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_867]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_2130,plain,
% 3.58/1.03      ( v2_struct_0(sK0) = iProver_top
% 3.58/1.03      | l1_pre_topc(sK0) != iProver_top
% 3.58/1.03      | sP0_iProver_split != iProver_top ),
% 3.58/1.03      inference(equality_resolution,[status(thm)],[c_1526]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_2680,plain,
% 3.58/1.03      ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.58/1.03      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.58/1.03      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.58/1.03      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.58/1.03      | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
% 3.58/1.03      inference(global_propositional_subsumption,
% 3.58/1.03                [status(thm)],
% 3.58/1.03                [c_2309,c_34,c_36,c_2130]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_2681,plain,
% 3.58/1.03      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 3.58/1.03      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.58/1.03      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.58/1.03      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.58/1.03      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 3.58/1.03      inference(renaming,[status(thm)],[c_2680]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_5192,plain,
% 3.58/1.03      ( k7_relat_1(sK3,u1_struct_0(sK1)) != sK3
% 3.58/1.03      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.58/1.03      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 3.58/1.03      inference(demodulation,[status(thm)],[c_5186,c_2681]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_2393,plain,
% 3.58/1.03      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
% 3.58/1.03      inference(superposition,[status(thm)],[c_1541,c_1547]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_5,plain,
% 3.58/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.58/1.03      | ~ v1_relat_1(X1)
% 3.58/1.03      | v1_relat_1(X0) ),
% 3.58/1.03      inference(cnf_transformation,[],[f55]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_3,plain,
% 3.58/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.58/1.03      inference(cnf_transformation,[],[f54]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_244,plain,
% 3.58/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.58/1.03      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_245,plain,
% 3.58/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.58/1.03      inference(renaming,[status(thm)],[c_244]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_313,plain,
% 3.58/1.03      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.58/1.03      inference(bin_hyper_res,[status(thm)],[c_5,c_245]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_1530,plain,
% 3.58/1.03      ( r1_tarski(X0,X1) != iProver_top
% 3.58/1.03      | v1_relat_1(X1) != iProver_top
% 3.58/1.03      | v1_relat_1(X0) = iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_2759,plain,
% 3.58/1.03      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
% 3.58/1.03      | v1_relat_1(sK3) = iProver_top ),
% 3.58/1.03      inference(superposition,[status(thm)],[c_2393,c_1530]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_6,plain,
% 3.58/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.58/1.03      inference(cnf_transformation,[],[f56]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_3148,plain,
% 3.58/1.03      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 3.58/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_3149,plain,
% 3.58/1.03      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_3148]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_3518,plain,
% 3.58/1.03      ( v1_relat_1(sK3) = iProver_top ),
% 3.58/1.03      inference(global_propositional_subsumption,
% 3.58/1.03                [status(thm)],
% 3.58/1.03                [c_2759,c_3149]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_8,plain,
% 3.58/1.03      ( v4_relat_1(X0,X1)
% 3.58/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.58/1.03      inference(cnf_transformation,[],[f58]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_7,plain,
% 3.58/1.03      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.58/1.03      inference(cnf_transformation,[],[f57]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_427,plain,
% 3.58/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.58/1.03      | ~ v1_relat_1(X0)
% 3.58/1.03      | k7_relat_1(X0,X1) = X0 ),
% 3.58/1.03      inference(resolution,[status(thm)],[c_8,c_7]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_1529,plain,
% 3.58/1.03      ( k7_relat_1(X0,X1) = X0
% 3.58/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.58/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_2312,plain,
% 3.58/1.03      ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3
% 3.58/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.58/1.03      inference(superposition,[status(thm)],[c_1541,c_1529]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_3522,plain,
% 3.58/1.03      ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
% 3.58/1.03      inference(superposition,[status(thm)],[c_3518,c_2312]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_5196,plain,
% 3.58/1.03      ( sK3 != sK3
% 3.58/1.03      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.58/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 3.58/1.03      inference(light_normalisation,[status(thm)],[c_5192,c_3522]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_5197,plain,
% 3.58/1.03      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.58/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 3.58/1.03      inference(equality_resolution_simp,[status(thm)],[c_5196]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(c_44,plain,
% 3.58/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 3.58/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.58/1.03  
% 3.58/1.03  cnf(contradiction,plain,
% 3.58/1.03      ( $false ),
% 3.58/1.03      inference(minisat,[status(thm)],[c_5197,c_44,c_43]) ).
% 3.58/1.03  
% 3.58/1.03  
% 3.58/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.58/1.03  
% 3.58/1.03  ------                               Statistics
% 3.58/1.03  
% 3.58/1.03  ------ General
% 3.58/1.03  
% 3.58/1.03  abstr_ref_over_cycles:                  0
% 3.58/1.03  abstr_ref_under_cycles:                 0
% 3.58/1.03  gc_basic_clause_elim:                   0
% 3.58/1.03  forced_gc_time:                         0
% 3.58/1.03  parsing_time:                           0.022
% 3.58/1.03  unif_index_cands_time:                  0.
% 3.58/1.03  unif_index_add_time:                    0.
% 3.58/1.03  orderings_time:                         0.
% 3.58/1.03  out_proof_time:                         0.018
% 3.58/1.03  total_time:                             0.335
% 3.58/1.03  num_of_symbols:                         57
% 3.58/1.03  num_of_terms:                           3989
% 3.58/1.03  
% 3.58/1.03  ------ Preprocessing
% 3.58/1.03  
% 3.58/1.03  num_of_splits:                          1
% 3.58/1.03  num_of_split_atoms:                     1
% 3.58/1.03  num_of_reused_defs:                     0
% 3.58/1.03  num_eq_ax_congr_red:                    14
% 3.58/1.03  num_of_sem_filtered_clauses:            1
% 3.58/1.03  num_of_subtypes:                        0
% 3.58/1.03  monotx_restored_types:                  0
% 3.58/1.03  sat_num_of_epr_types:                   0
% 3.58/1.03  sat_num_of_non_cyclic_types:            0
% 3.58/1.03  sat_guarded_non_collapsed_types:        0
% 3.58/1.03  num_pure_diseq_elim:                    0
% 3.58/1.03  simp_replaced_by:                       0
% 3.58/1.03  res_preprocessed:                       147
% 3.58/1.03  prep_upred:                             0
% 3.58/1.03  prep_unflattend:                        13
% 3.58/1.03  smt_new_axioms:                         0
% 3.58/1.03  pred_elim_cands:                        8
% 3.58/1.03  pred_elim:                              5
% 3.58/1.03  pred_elim_cl:                           6
% 3.58/1.03  pred_elim_cycles:                       7
% 3.58/1.03  merged_defs:                            8
% 3.58/1.03  merged_defs_ncl:                        0
% 3.58/1.03  bin_hyper_res:                          9
% 3.58/1.03  prep_cycles:                            4
% 3.58/1.03  pred_elim_time:                         0.006
% 3.58/1.03  splitting_time:                         0.
% 3.58/1.03  sem_filter_time:                        0.
% 3.58/1.03  monotx_time:                            0.
% 3.58/1.03  subtype_inf_time:                       0.
% 3.58/1.03  
% 3.58/1.03  ------ Problem properties
% 3.58/1.03  
% 3.58/1.03  clauses:                                27
% 3.58/1.03  conjectures:                            11
% 3.58/1.03  epr:                                    13
% 3.58/1.03  horn:                                   26
% 3.58/1.03  ground:                                 12
% 3.58/1.03  unary:                                  13
% 3.58/1.03  binary:                                 4
% 3.58/1.03  lits:                                   62
% 3.58/1.03  lits_eq:                                7
% 3.58/1.03  fd_pure:                                0
% 3.58/1.03  fd_pseudo:                              0
% 3.58/1.03  fd_cond:                                0
% 3.58/1.03  fd_pseudo_cond:                         1
% 3.58/1.03  ac_symbols:                             0
% 3.58/1.03  
% 3.58/1.03  ------ Propositional Solver
% 3.58/1.03  
% 3.58/1.03  prop_solver_calls:                      33
% 3.58/1.03  prop_fast_solver_calls:                 1155
% 3.58/1.03  smt_solver_calls:                       0
% 3.58/1.03  smt_fast_solver_calls:                  0
% 3.58/1.03  prop_num_of_clauses:                    1804
% 3.58/1.03  prop_preprocess_simplified:             5709
% 3.58/1.03  prop_fo_subsumed:                       31
% 3.58/1.03  prop_solver_time:                       0.
% 3.58/1.03  smt_solver_time:                        0.
% 3.58/1.03  smt_fast_solver_time:                   0.
% 3.58/1.03  prop_fast_solver_time:                  0.
% 3.58/1.03  prop_unsat_core_time:                   0.
% 3.58/1.03  
% 3.58/1.03  ------ QBF
% 3.58/1.03  
% 3.58/1.03  qbf_q_res:                              0
% 3.58/1.03  qbf_num_tautologies:                    0
% 3.58/1.03  qbf_prep_cycles:                        0
% 3.58/1.03  
% 3.58/1.03  ------ BMC1
% 3.58/1.03  
% 3.58/1.03  bmc1_current_bound:                     -1
% 3.58/1.03  bmc1_last_solved_bound:                 -1
% 3.58/1.03  bmc1_unsat_core_size:                   -1
% 3.58/1.03  bmc1_unsat_core_parents_size:           -1
% 3.58/1.03  bmc1_merge_next_fun:                    0
% 3.58/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.58/1.03  
% 3.58/1.03  ------ Instantiation
% 3.58/1.03  
% 3.58/1.03  inst_num_of_clauses:                    543
% 3.58/1.03  inst_num_in_passive:                    64
% 3.58/1.03  inst_num_in_active:                     416
% 3.58/1.03  inst_num_in_unprocessed:                63
% 3.58/1.03  inst_num_of_loops:                      440
% 3.58/1.03  inst_num_of_learning_restarts:          0
% 3.58/1.03  inst_num_moves_active_passive:          17
% 3.58/1.03  inst_lit_activity:                      0
% 3.58/1.03  inst_lit_activity_moves:                0
% 3.58/1.03  inst_num_tautologies:                   0
% 3.58/1.03  inst_num_prop_implied:                  0
% 3.58/1.03  inst_num_existing_simplified:           0
% 3.58/1.03  inst_num_eq_res_simplified:             0
% 3.58/1.03  inst_num_child_elim:                    0
% 3.58/1.03  inst_num_of_dismatching_blockings:      266
% 3.58/1.03  inst_num_of_non_proper_insts:           967
% 3.58/1.03  inst_num_of_duplicates:                 0
% 3.58/1.03  inst_inst_num_from_inst_to_res:         0
% 3.58/1.03  inst_dismatching_checking_time:         0.
% 3.58/1.03  
% 3.58/1.03  ------ Resolution
% 3.58/1.03  
% 3.58/1.03  res_num_of_clauses:                     0
% 3.58/1.03  res_num_in_passive:                     0
% 3.58/1.03  res_num_in_active:                      0
% 3.58/1.03  res_num_of_loops:                       151
% 3.58/1.03  res_forward_subset_subsumed:            161
% 3.58/1.03  res_backward_subset_subsumed:           0
% 3.58/1.03  res_forward_subsumed:                   0
% 3.58/1.03  res_backward_subsumed:                  0
% 3.58/1.03  res_forward_subsumption_resolution:     0
% 3.58/1.03  res_backward_subsumption_resolution:    0
% 3.58/1.03  res_clause_to_clause_subsumption:       557
% 3.58/1.03  res_orphan_elimination:                 0
% 3.58/1.03  res_tautology_del:                      155
% 3.58/1.03  res_num_eq_res_simplified:              0
% 3.58/1.03  res_num_sel_changes:                    0
% 3.58/1.03  res_moves_from_active_to_pass:          0
% 3.58/1.03  
% 3.58/1.03  ------ Superposition
% 3.58/1.03  
% 3.58/1.03  sup_time_total:                         0.
% 3.58/1.03  sup_time_generating:                    0.
% 3.58/1.03  sup_time_sim_full:                      0.
% 3.58/1.03  sup_time_sim_immed:                     0.
% 3.58/1.03  
% 3.58/1.03  sup_num_of_clauses:                     114
% 3.58/1.03  sup_num_in_active:                      75
% 3.58/1.03  sup_num_in_passive:                     39
% 3.58/1.03  sup_num_of_loops:                       86
% 3.58/1.03  sup_fw_superposition:                   137
% 3.58/1.03  sup_bw_superposition:                   93
% 3.58/1.03  sup_immediate_simplified:               40
% 3.58/1.03  sup_given_eliminated:                   0
% 3.58/1.03  comparisons_done:                       0
% 3.58/1.03  comparisons_avoided:                    0
% 3.58/1.03  
% 3.58/1.03  ------ Simplifications
% 3.58/1.03  
% 3.58/1.03  
% 3.58/1.03  sim_fw_subset_subsumed:                 15
% 3.58/1.03  sim_bw_subset_subsumed:                 6
% 3.58/1.03  sim_fw_subsumed:                        5
% 3.58/1.03  sim_bw_subsumed:                        11
% 3.58/1.03  sim_fw_subsumption_res:                 0
% 3.58/1.03  sim_bw_subsumption_res:                 0
% 3.58/1.03  sim_tautology_del:                      30
% 3.58/1.03  sim_eq_tautology_del:                   5
% 3.58/1.03  sim_eq_res_simp:                        1
% 3.58/1.03  sim_fw_demodulated:                     1
% 3.58/1.03  sim_bw_demodulated:                     9
% 3.58/1.03  sim_light_normalised:                   14
% 3.58/1.03  sim_joinable_taut:                      0
% 3.58/1.03  sim_joinable_simp:                      0
% 3.58/1.03  sim_ac_normalised:                      0
% 3.58/1.03  sim_smt_subsumption:                    0
% 3.58/1.03  
%------------------------------------------------------------------------------
