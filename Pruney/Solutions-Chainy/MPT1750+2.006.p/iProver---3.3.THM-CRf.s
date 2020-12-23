%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:22 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  215 (2098 expanded)
%              Number of clauses        :  142 ( 574 expanded)
%              Number of leaves         :   21 ( 705 expanded)
%              Depth                    :   25
%              Number of atoms          :  845 (19468 expanded)
%              Number of equality atoms :  280 (2400 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

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
    inference(ennf_transformation,[],[f16])).

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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f50,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f49,f48,f47,f46])).

fof(f83,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

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
    inference(nnf_transformation,[],[f37])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f50])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

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
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f73,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f84,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

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
    inference(nnf_transformation,[],[f32])).

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

fof(f88,plain,(
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

cnf(c_18,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1036,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_248,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_10])).

cnf(c_249,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_248])).

cnf(c_1021,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_249])).

cnf(c_22,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_12,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1040,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2351,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1040])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_39,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1460,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_10,c_26])).

cnf(c_1461,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1460])).

cnf(c_2501,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2351,c_39,c_1461])).

cnf(c_2502,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_2501])).

cnf(c_2509,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1021,c_2502])).

cnf(c_2835,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2509,c_39])).

cnf(c_2836,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2835])).

cnf(c_2843,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1036,c_2836])).

cnf(c_50,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_52,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_62,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_64,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_2373,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2351])).

cnf(c_4834,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2843,c_39,c_52,c_64,c_1461,c_2373])).

cnf(c_1435,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1021])).

cnf(c_1740,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1435,c_39,c_1461])).

cnf(c_1741,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1740])).

cnf(c_2350,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1741,c_1040])).

cnf(c_2702,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2350,c_39])).

cnf(c_2703,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2702])).

cnf(c_4842,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4834,c_2703])).

cnf(c_1029,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1035,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3088,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1029,c_1035])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_38,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3879,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3088,c_38,c_39])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1051,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3888,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK2)
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3879,c_1051])).

cnf(c_4341,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X0,sK1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_19,c_26])).

cnf(c_4342,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4341])).

cnf(c_5461,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3888,c_38,c_39,c_2509,c_4342])).

cnf(c_5462,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK2)
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5461])).

cnf(c_5472,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_pre_topc(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4842,c_5462])).

cnf(c_41,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8499,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5472,c_41])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1032,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1037,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4144,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1032,c_1037])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_34,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_35,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_36,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_37,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_42,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_43,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_44,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1426,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1553,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1426])).

cnf(c_1554,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1553])).

cnf(c_4472,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4144,c_34,c_35,c_36,c_37,c_38,c_39,c_42,c_43,c_44,c_1554])).

cnf(c_4473,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4472])).

cnf(c_4481,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1029,c_4473])).

cnf(c_8503,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_8499,c_4481])).

cnf(c_4862,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = k2_tmap_1(sK1,sK0,sK3,sK1) ),
    inference(superposition,[status(thm)],[c_4842,c_4473])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1047,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5005,plain,
    ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4862,c_1047])).

cnf(c_51,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1555,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = k2_tmap_1(sK1,sK0,sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_1553])).

cnf(c_440,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1931,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_1390,plain,
    ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1506,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1390])).

cnf(c_2406,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_2407,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2406])).

cnf(c_441,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1842,plain,
    ( X0 != X1
    | X0 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_2624,plain,
    ( X0 != k2_tmap_1(sK1,sK0,sK3,X1)
    | X0 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X1))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X1)) != k2_tmap_1(sK1,sK0,sK3,X1) ),
    inference(instantiation,[status(thm)],[c_1842])).

cnf(c_2812,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) != k2_tmap_1(sK1,sK0,sK3,X0)
    | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) != k2_tmap_1(sK1,sK0,sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2624])).

cnf(c_2814,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK1) != k2_tmap_1(sK1,sK0,sK3,sK1)
    | k2_tmap_1(sK1,sK0,sK3,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) != k2_tmap_1(sK1,sK0,sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_2812])).

cnf(c_2813,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k2_tmap_1(sK1,sK0,sK3,X0) ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_2815,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK1) = k2_tmap_1(sK1,sK0,sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_2813])).

cnf(c_446,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1593,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | X0 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2)
    | X1 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_446])).

cnf(c_1930,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | X0 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1593])).

cnf(c_4437,plain,
    ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_tmap_1(sK1,sK0,sK3,X0) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1930])).

cnf(c_4443,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4437])).

cnf(c_4445,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK1) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4443])).

cnf(c_7992,plain,
    ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5005,c_33,c_32,c_31,c_30,c_29,c_28,c_25,c_42,c_24,c_23,c_44,c_51,c_1555,c_1931,c_2407,c_2814,c_2815,c_4445])).

cnf(c_4,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1048,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3531,plain,
    ( sK3 = X0
    | r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1032,c_1048])).

cnf(c_8001,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK1) = sK3
    | r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7992,c_3531])).

cnf(c_48,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1489,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_7,plain,
    ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3),X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(X0,X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1416,plain,
    ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,sK3,X2),sK3)
    | ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(X0,X2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1511,plain,
    ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ r1_tarski(u1_struct_0(sK1),X0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1416])).

cnf(c_1720,plain,
    ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_1467,plain,
    ( ~ r2_relset_1(X0,X1,X2,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = sK3 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1681,plain,
    ( ~ r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1467])).

cnf(c_1782,plain,
    ( ~ r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),sK3)
    | ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = sK3 ),
    inference(instantiation,[status(thm)],[c_1681])).

cnf(c_1679,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_2061,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1679])).

cnf(c_2681,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) != sK3
    | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2061])).

cnf(c_1478,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_4258,plain,
    ( X0 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X1))
    | X0 = sK3
    | sK3 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_1478])).

cnf(c_6125,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
    | k2_tmap_1(sK1,sK0,sK3,X0) = sK3
    | sK3 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_4258])).

cnf(c_6126,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK1) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
    | k2_tmap_1(sK1,sK0,sK3,sK1) = sK3
    | sK3 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_6125])).

cnf(c_8321,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK1) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8001,c_33,c_32,c_31,c_30,c_29,c_28,c_25,c_24,c_23,c_48,c_51,c_1489,c_1555,c_1720,c_1782,c_2406,c_2681,c_2814,c_2815,c_6126])).

cnf(c_8328,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = sK3 ),
    inference(demodulation,[status(thm)],[c_8321,c_4862])).

cnf(c_8518,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_8503,c_8328])).

cnf(c_21,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1033,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8505,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8499,c_1033])).

cnf(c_8519,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8518,c_8505])).

cnf(c_9,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1778,plain,
    ( l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1779,plain,
    ( l1_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1778])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1711,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1712,plain,
    ( v2_struct_0(sK0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) != iProver_top
    | l1_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1711])).

cnf(c_15,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1421,plain,
    ( r1_funct_2(X0,X1,X2,X3,sK3,sK3)
    | ~ v1_funct_2(sK3,X0,X1)
    | ~ v1_funct_2(sK3,X2,X3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1548,plain,
    ( r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | ~ v1_funct_2(sK3,X0,X1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(X1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1421])).

cnf(c_1603,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1548])).

cnf(c_1604,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1603])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8519,c_1779,c_1712,c_1604,c_44,c_43,c_42,c_36,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:07:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.87/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/0.99  
% 3.87/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.87/0.99  
% 3.87/0.99  ------  iProver source info
% 3.87/0.99  
% 3.87/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.87/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.87/0.99  git: non_committed_changes: false
% 3.87/0.99  git: last_make_outside_of_git: false
% 3.87/0.99  
% 3.87/0.99  ------ 
% 3.87/0.99  ------ Parsing...
% 3.87/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.87/0.99  
% 3.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.87/0.99  
% 3.87/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.87/0.99  
% 3.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.87/0.99  ------ Proving...
% 3.87/0.99  ------ Problem Properties 
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  clauses                                 32
% 3.87/0.99  conjectures                             13
% 3.87/0.99  EPR                                     15
% 3.87/0.99  Horn                                    29
% 3.87/0.99  unary                                   14
% 3.87/0.99  binary                                  3
% 3.87/0.99  lits                                    95
% 3.87/0.99  lits eq                                 5
% 3.87/0.99  fd_pure                                 0
% 3.87/0.99  fd_pseudo                               0
% 3.87/0.99  fd_cond                                 0
% 3.87/0.99  fd_pseudo_cond                          3
% 3.87/0.99  AC symbols                              0
% 3.87/0.99  
% 3.87/0.99  ------ Input Options Time Limit: Unbounded
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  ------ 
% 3.87/0.99  Current options:
% 3.87/0.99  ------ 
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  ------ Proving...
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  % SZS status Theorem for theBenchmark.p
% 3.87/0.99  
% 3.87/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.87/0.99  
% 3.87/0.99  fof(f13,axiom,(
% 3.87/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f35,plain,(
% 3.87/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.87/0.99    inference(ennf_transformation,[],[f13])).
% 3.87/0.99  
% 3.87/0.99  fof(f69,plain,(
% 3.87/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f35])).
% 3.87/0.99  
% 3.87/0.99  fof(f10,axiom,(
% 3.87/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f30,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.87/0.99    inference(ennf_transformation,[],[f10])).
% 3.87/0.99  
% 3.87/0.99  fof(f43,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.87/0.99    inference(nnf_transformation,[],[f30])).
% 3.87/0.99  
% 3.87/0.99  fof(f64,plain,(
% 3.87/0.99    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f43])).
% 3.87/0.99  
% 3.87/0.99  fof(f7,axiom,(
% 3.87/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f26,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.87/0.99    inference(ennf_transformation,[],[f7])).
% 3.87/0.99  
% 3.87/0.99  fof(f61,plain,(
% 3.87/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f26])).
% 3.87/0.99  
% 3.87/0.99  fof(f15,conjecture,(
% 3.87/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f16,negated_conjecture,(
% 3.87/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 3.87/0.99    inference(negated_conjecture,[],[f15])).
% 3.87/0.99  
% 3.87/0.99  fof(f38,plain,(
% 3.87/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.87/0.99    inference(ennf_transformation,[],[f16])).
% 3.87/0.99  
% 3.87/0.99  fof(f39,plain,(
% 3.87/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.87/0.99    inference(flattening,[],[f38])).
% 3.87/0.99  
% 3.87/0.99  fof(f49,plain,(
% 3.87/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 3.87/0.99    introduced(choice_axiom,[])).
% 3.87/0.99  
% 3.87/0.99  fof(f48,plain,(
% 3.87/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 3.87/0.99    introduced(choice_axiom,[])).
% 3.87/0.99  
% 3.87/0.99  fof(f47,plain,(
% 3.87/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.87/0.99    introduced(choice_axiom,[])).
% 3.87/0.99  
% 3.87/0.99  fof(f46,plain,(
% 3.87/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.87/0.99    introduced(choice_axiom,[])).
% 3.87/0.99  
% 3.87/0.99  fof(f50,plain,(
% 3.87/0.99    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f49,f48,f47,f46])).
% 3.87/0.99  
% 3.87/0.99  fof(f83,plain,(
% 3.87/0.99    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 3.87/0.99    inference(cnf_transformation,[],[f50])).
% 3.87/0.99  
% 3.87/0.99  fof(f9,axiom,(
% 3.87/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f29,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.87/0.99    inference(ennf_transformation,[],[f9])).
% 3.87/0.99  
% 3.87/0.99  fof(f63,plain,(
% 3.87/0.99    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f29])).
% 3.87/0.99  
% 3.87/0.99  fof(f77,plain,(
% 3.87/0.99    l1_pre_topc(sK1)),
% 3.87/0.99    inference(cnf_transformation,[],[f50])).
% 3.87/0.99  
% 3.87/0.99  fof(f79,plain,(
% 3.87/0.99    m1_pre_topc(sK2,sK1)),
% 3.87/0.99    inference(cnf_transformation,[],[f50])).
% 3.87/0.99  
% 3.87/0.99  fof(f14,axiom,(
% 3.87/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f36,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.87/0.99    inference(ennf_transformation,[],[f14])).
% 3.87/0.99  
% 3.87/0.99  fof(f37,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.87/0.99    inference(flattening,[],[f36])).
% 3.87/0.99  
% 3.87/0.99  fof(f45,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.87/0.99    inference(nnf_transformation,[],[f37])).
% 3.87/0.99  
% 3.87/0.99  fof(f71,plain,(
% 3.87/0.99    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f45])).
% 3.87/0.99  
% 3.87/0.99  fof(f76,plain,(
% 3.87/0.99    v2_pre_topc(sK1)),
% 3.87/0.99    inference(cnf_transformation,[],[f50])).
% 3.87/0.99  
% 3.87/0.99  fof(f1,axiom,(
% 3.87/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f40,plain,(
% 3.87/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.87/0.99    inference(nnf_transformation,[],[f1])).
% 3.87/0.99  
% 3.87/0.99  fof(f41,plain,(
% 3.87/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.87/0.99    inference(flattening,[],[f40])).
% 3.87/0.99  
% 3.87/0.99  fof(f53,plain,(
% 3.87/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f41])).
% 3.87/0.99  
% 3.87/0.99  fof(f82,plain,(
% 3.87/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 3.87/0.99    inference(cnf_transformation,[],[f50])).
% 3.87/0.99  
% 3.87/0.99  fof(f12,axiom,(
% 3.87/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f33,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.87/0.99    inference(ennf_transformation,[],[f12])).
% 3.87/0.99  
% 3.87/0.99  fof(f34,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.87/0.99    inference(flattening,[],[f33])).
% 3.87/0.99  
% 3.87/0.99  fof(f68,plain,(
% 3.87/0.99    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f34])).
% 3.87/0.99  
% 3.87/0.99  fof(f72,plain,(
% 3.87/0.99    ~v2_struct_0(sK0)),
% 3.87/0.99    inference(cnf_transformation,[],[f50])).
% 3.87/0.99  
% 3.87/0.99  fof(f73,plain,(
% 3.87/0.99    v2_pre_topc(sK0)),
% 3.87/0.99    inference(cnf_transformation,[],[f50])).
% 3.87/0.99  
% 3.87/0.99  fof(f74,plain,(
% 3.87/0.99    l1_pre_topc(sK0)),
% 3.87/0.99    inference(cnf_transformation,[],[f50])).
% 3.87/0.99  
% 3.87/0.99  fof(f75,plain,(
% 3.87/0.99    ~v2_struct_0(sK1)),
% 3.87/0.99    inference(cnf_transformation,[],[f50])).
% 3.87/0.99  
% 3.87/0.99  fof(f80,plain,(
% 3.87/0.99    v1_funct_1(sK3)),
% 3.87/0.99    inference(cnf_transformation,[],[f50])).
% 3.87/0.99  
% 3.87/0.99  fof(f81,plain,(
% 3.87/0.99    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 3.87/0.99    inference(cnf_transformation,[],[f50])).
% 3.87/0.99  
% 3.87/0.99  fof(f3,axiom,(
% 3.87/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f19,plain,(
% 3.87/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.87/0.99    inference(ennf_transformation,[],[f3])).
% 3.87/0.99  
% 3.87/0.99  fof(f20,plain,(
% 3.87/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.87/0.99    inference(flattening,[],[f19])).
% 3.87/0.99  
% 3.87/0.99  fof(f57,plain,(
% 3.87/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f20])).
% 3.87/0.99  
% 3.87/0.99  fof(f2,axiom,(
% 3.87/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f17,plain,(
% 3.87/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.87/0.99    inference(ennf_transformation,[],[f2])).
% 3.87/0.99  
% 3.87/0.99  fof(f18,plain,(
% 3.87/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/0.99    inference(flattening,[],[f17])).
% 3.87/0.99  
% 3.87/0.99  fof(f42,plain,(
% 3.87/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/0.99    inference(nnf_transformation,[],[f18])).
% 3.87/0.99  
% 3.87/0.99  fof(f54,plain,(
% 3.87/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.87/0.99    inference(cnf_transformation,[],[f42])).
% 3.87/0.99  
% 3.87/0.99  fof(f4,axiom,(
% 3.87/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f21,plain,(
% 3.87/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.87/0.99    inference(ennf_transformation,[],[f4])).
% 3.87/0.99  
% 3.87/0.99  fof(f22,plain,(
% 3.87/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.87/0.99    inference(flattening,[],[f21])).
% 3.87/0.99  
% 3.87/0.99  fof(f58,plain,(
% 3.87/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f22])).
% 3.87/0.99  
% 3.87/0.99  fof(f84,plain,(
% 3.87/0.99    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 3.87/0.99    inference(cnf_transformation,[],[f50])).
% 3.87/0.99  
% 3.87/0.99  fof(f6,axiom,(
% 3.87/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f25,plain,(
% 3.87/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.87/0.99    inference(ennf_transformation,[],[f6])).
% 3.87/0.99  
% 3.87/0.99  fof(f60,plain,(
% 3.87/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f25])).
% 3.87/0.99  
% 3.87/0.99  fof(f8,axiom,(
% 3.87/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f27,plain,(
% 3.87/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.87/0.99    inference(ennf_transformation,[],[f8])).
% 3.87/0.99  
% 3.87/0.99  fof(f28,plain,(
% 3.87/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.87/0.99    inference(flattening,[],[f27])).
% 3.87/0.99  
% 3.87/0.99  fof(f62,plain,(
% 3.87/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f28])).
% 3.87/0.99  
% 3.87/0.99  fof(f11,axiom,(
% 3.87/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f31,plain,(
% 3.87/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.87/0.99    inference(ennf_transformation,[],[f11])).
% 3.87/0.99  
% 3.87/0.99  fof(f32,plain,(
% 3.87/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.87/0.99    inference(flattening,[],[f31])).
% 3.87/0.99  
% 3.87/0.99  fof(f44,plain,(
% 3.87/0.99    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.87/0.99    inference(nnf_transformation,[],[f32])).
% 3.87/0.99  
% 3.87/0.99  fof(f67,plain,(
% 3.87/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f44])).
% 3.87/0.99  
% 3.87/0.99  fof(f88,plain,(
% 3.87/0.99    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.87/0.99    inference(equality_resolution,[],[f67])).
% 3.87/0.99  
% 3.87/0.99  cnf(c_18,plain,
% 3.87/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1036,plain,
% 3.87/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.87/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_14,plain,
% 3.87/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.87/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.87/0.99      | ~ l1_pre_topc(X0)
% 3.87/0.99      | ~ l1_pre_topc(X1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_10,plain,
% 3.87/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_248,plain,
% 3.87/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.87/0.99      | ~ m1_pre_topc(X0,X1)
% 3.87/0.99      | ~ l1_pre_topc(X1) ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_14,c_10]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_249,plain,
% 3.87/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.87/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.87/0.99      | ~ l1_pre_topc(X1) ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_248]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1021,plain,
% 3.87/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.87/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.87/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_249]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_22,negated_conjecture,
% 3.87/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.87/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_12,plain,
% 3.87/0.99      ( m1_pre_topc(X0,X1)
% 3.87/0.99      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.87/0.99      | ~ l1_pre_topc(X1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1040,plain,
% 3.87/0.99      ( m1_pre_topc(X0,X1) = iProver_top
% 3.87/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.87/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2351,plain,
% 3.87/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.87/0.99      | m1_pre_topc(X0,sK2) = iProver_top
% 3.87/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_22,c_1040]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_28,negated_conjecture,
% 3.87/0.99      ( l1_pre_topc(sK1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_39,plain,
% 3.87/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_26,negated_conjecture,
% 3.87/0.99      ( m1_pre_topc(sK2,sK1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1460,plain,
% 3.87/0.99      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK1) ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_10,c_26]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1461,plain,
% 3.87/0.99      ( l1_pre_topc(sK2) = iProver_top
% 3.87/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1460]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2501,plain,
% 3.87/0.99      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.87/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_2351,c_39,c_1461]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2502,plain,
% 3.87/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.87/0.99      | m1_pre_topc(X0,sK2) = iProver_top ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_2501]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2509,plain,
% 3.87/0.99      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.87/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.87/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1021,c_2502]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2835,plain,
% 3.87/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.87/0.99      | m1_pre_topc(X0,sK2) = iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_2509,c_39]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2836,plain,
% 3.87/0.99      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.87/0.99      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_2835]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2843,plain,
% 3.87/0.99      ( m1_pre_topc(sK1,sK2) = iProver_top
% 3.87/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1036,c_2836]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_50,plain,
% 3.87/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.87/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_52,plain,
% 3.87/0.99      ( m1_pre_topc(sK1,sK1) = iProver_top
% 3.87/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_50]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_62,plain,
% 3.87/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.87/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.87/0.99      | l1_pre_topc(X1) != iProver_top
% 3.87/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_64,plain,
% 3.87/0.99      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.87/0.99      | m1_pre_topc(sK1,sK1) != iProver_top
% 3.87/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_62]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2373,plain,
% 3.87/0.99      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.87/0.99      | m1_pre_topc(sK1,sK2) = iProver_top
% 3.87/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2351]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4834,plain,
% 3.87/0.99      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_2843,c_39,c_52,c_64,c_1461,c_2373]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1435,plain,
% 3.87/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.87/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.87/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_22,c_1021]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1740,plain,
% 3.87/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.87/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_1435,c_39,c_1461]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1741,plain,
% 3.87/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.87/0.99      | m1_pre_topc(X0,sK2) != iProver_top ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_1740]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2350,plain,
% 3.87/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.87/0.99      | m1_pre_topc(X0,sK1) = iProver_top
% 3.87/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1741,c_1040]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2702,plain,
% 3.87/0.99      ( m1_pre_topc(X0,sK1) = iProver_top
% 3.87/0.99      | m1_pre_topc(X0,sK2) != iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_2350,c_39]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2703,plain,
% 3.87/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.87/0.99      | m1_pre_topc(X0,sK1) = iProver_top ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_2702]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4842,plain,
% 3.87/0.99      ( m1_pre_topc(sK1,sK1) = iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_4834,c_2703]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1029,plain,
% 3.87/0.99      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_19,plain,
% 3.87/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.87/0.99      | ~ m1_pre_topc(X0,X2)
% 3.87/0.99      | ~ m1_pre_topc(X2,X1)
% 3.87/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 3.87/0.99      | ~ l1_pre_topc(X1)
% 3.87/0.99      | ~ v2_pre_topc(X1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1035,plain,
% 3.87/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.87/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 3.87/0.99      | m1_pre_topc(X0,X2) != iProver_top
% 3.87/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 3.87/0.99      | l1_pre_topc(X1) != iProver_top
% 3.87/0.99      | v2_pre_topc(X1) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3088,plain,
% 3.87/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.87/0.99      | m1_pre_topc(sK2,X0) != iProver_top
% 3.87/0.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 3.87/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.87/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1029,c_1035]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_29,negated_conjecture,
% 3.87/0.99      ( v2_pre_topc(sK1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_38,plain,
% 3.87/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3879,plain,
% 3.87/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.87/0.99      | m1_pre_topc(sK2,X0) != iProver_top
% 3.87/0.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_3088,c_38,c_39]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_0,plain,
% 3.87/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.87/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1051,plain,
% 3.87/0.99      ( X0 = X1
% 3.87/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.87/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3888,plain,
% 3.87/0.99      ( u1_struct_0(X0) = u1_struct_0(sK2)
% 3.87/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.87/0.99      | m1_pre_topc(sK2,X0) != iProver_top
% 3.87/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_3879,c_1051]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4341,plain,
% 3.87/0.99      ( ~ m1_pre_topc(X0,sK2)
% 3.87/0.99      | ~ m1_pre_topc(X0,sK1)
% 3.87/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
% 3.87/0.99      | ~ l1_pre_topc(sK1)
% 3.87/0.99      | ~ v2_pre_topc(sK1) ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_19,c_26]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4342,plain,
% 3.87/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.87/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.87/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top
% 3.87/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.87/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_4341]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5461,plain,
% 3.87/0.99      ( m1_pre_topc(sK2,X0) != iProver_top
% 3.87/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.87/0.99      | u1_struct_0(X0) = u1_struct_0(sK2) ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_3888,c_38,c_39,c_2509,c_4342]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5462,plain,
% 3.87/0.99      ( u1_struct_0(X0) = u1_struct_0(sK2)
% 3.87/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.87/0.99      | m1_pre_topc(sK2,X0) != iProver_top ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_5461]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5472,plain,
% 3.87/0.99      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 3.87/0.99      | m1_pre_topc(sK2,sK1) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_4842,c_5462]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_41,plain,
% 3.87/0.99      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8499,plain,
% 3.87/0.99      ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_5472,c_41]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_23,negated_conjecture,
% 3.87/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 3.87/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1032,plain,
% 3.87/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_17,plain,
% 3.87/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.87/0.99      | ~ m1_pre_topc(X3,X1)
% 3.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.87/0.99      | v2_struct_0(X1)
% 3.87/0.99      | v2_struct_0(X2)
% 3.87/0.99      | ~ l1_pre_topc(X1)
% 3.87/0.99      | ~ l1_pre_topc(X2)
% 3.87/0.99      | ~ v2_pre_topc(X1)
% 3.87/0.99      | ~ v2_pre_topc(X2)
% 3.87/0.99      | ~ v1_funct_1(X0)
% 3.87/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.87/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1037,plain,
% 3.87/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
% 3.87/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.87/0.99      | m1_pre_topc(X3,X0) != iProver_top
% 3.87/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.87/0.99      | v2_struct_0(X0) = iProver_top
% 3.87/0.99      | v2_struct_0(X1) = iProver_top
% 3.87/0.99      | l1_pre_topc(X0) != iProver_top
% 3.87/0.99      | l1_pre_topc(X1) != iProver_top
% 3.87/0.99      | v2_pre_topc(X0) != iProver_top
% 3.87/0.99      | v2_pre_topc(X1) != iProver_top
% 3.87/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4144,plain,
% 3.87/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 3.87/0.99      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.87/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.87/0.99      | v2_struct_0(sK0) = iProver_top
% 3.87/0.99      | v2_struct_0(sK1) = iProver_top
% 3.87/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.87/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.87/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.87/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.87/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1032,c_1037]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_33,negated_conjecture,
% 3.87/0.99      ( ~ v2_struct_0(sK0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_34,plain,
% 3.87/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_32,negated_conjecture,
% 3.87/0.99      ( v2_pre_topc(sK0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_35,plain,
% 3.87/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_31,negated_conjecture,
% 3.87/0.99      ( l1_pre_topc(sK0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_36,plain,
% 3.87/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_30,negated_conjecture,
% 3.87/0.99      ( ~ v2_struct_0(sK1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_37,plain,
% 3.87/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_25,negated_conjecture,
% 3.87/0.99      ( v1_funct_1(sK3) ),
% 3.87/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_42,plain,
% 3.87/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_24,negated_conjecture,
% 3.87/0.99      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 3.87/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_43,plain,
% 3.87/0.99      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_44,plain,
% 3.87/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1426,plain,
% 3.87/0.99      ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
% 3.87/0.99      | ~ m1_pre_topc(X2,X0)
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.87/0.99      | v2_struct_0(X0)
% 3.87/0.99      | v2_struct_0(X1)
% 3.87/0.99      | ~ l1_pre_topc(X0)
% 3.87/0.99      | ~ l1_pre_topc(X1)
% 3.87/0.99      | ~ v2_pre_topc(X0)
% 3.87/0.99      | ~ v2_pre_topc(X1)
% 3.87/0.99      | ~ v1_funct_1(sK3)
% 3.87/0.99      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1553,plain,
% 3.87/0.99      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 3.87/0.99      | ~ m1_pre_topc(X0,sK1)
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | v2_struct_0(sK0)
% 3.87/0.99      | v2_struct_0(sK1)
% 3.87/0.99      | ~ l1_pre_topc(sK0)
% 3.87/0.99      | ~ l1_pre_topc(sK1)
% 3.87/0.99      | ~ v2_pre_topc(sK0)
% 3.87/0.99      | ~ v2_pre_topc(sK1)
% 3.87/0.99      | ~ v1_funct_1(sK3)
% 3.87/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1426]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1554,plain,
% 3.87/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 3.87/0.99      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.87/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.87/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.87/0.99      | v2_struct_0(sK0) = iProver_top
% 3.87/0.99      | v2_struct_0(sK1) = iProver_top
% 3.87/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.87/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.87/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.87/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.87/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1553]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4472,plain,
% 3.87/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.87/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0) ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_4144,c_34,c_35,c_36,c_37,c_38,c_39,c_42,c_43,c_44,
% 3.87/0.99                 c_1554]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4473,plain,
% 3.87/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 3.87/0.99      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_4472]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4481,plain,
% 3.87/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1029,c_4473]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8503,plain,
% 3.87/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 3.87/0.99      inference(demodulation,[status(thm)],[c_8499,c_4481]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4862,plain,
% 3.87/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = k2_tmap_1(sK1,sK0,sK3,sK1) ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_4842,c_4473]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5,plain,
% 3.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.99      | ~ v1_funct_1(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1047,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.87/0.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.87/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5005,plain,
% 3.87/0.99      ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 3.87/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.87/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_4862,c_1047]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_51,plain,
% 3.87/0.99      ( m1_pre_topc(sK1,sK1) | ~ l1_pre_topc(sK1) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1555,plain,
% 3.87/0.99      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 3.87/0.99      | ~ m1_pre_topc(sK1,sK1)
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | v2_struct_0(sK0)
% 3.87/0.99      | v2_struct_0(sK1)
% 3.87/0.99      | ~ l1_pre_topc(sK0)
% 3.87/0.99      | ~ l1_pre_topc(sK1)
% 3.87/0.99      | ~ v2_pre_topc(sK0)
% 3.87/0.99      | ~ v2_pre_topc(sK1)
% 3.87/0.99      | ~ v1_funct_1(sK3)
% 3.87/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = k2_tmap_1(sK1,sK0,sK3,sK1) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1553]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_440,plain,( X0 = X0 ),theory(equality) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1931,plain,
% 3.87/0.99      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_440]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1390,plain,
% 3.87/0.99      ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.87/0.99      | ~ v1_funct_1(sK3) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1506,plain,
% 3.87/0.99      ( m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | ~ v1_funct_1(sK3) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1390]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2406,plain,
% 3.87/0.99      ( m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | ~ v1_funct_1(sK3) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1506]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2407,plain,
% 3.87/0.99      ( m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 3.87/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.87/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2406]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_441,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1842,plain,
% 3.87/0.99      ( X0 != X1
% 3.87/0.99      | X0 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2)
% 3.87/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2) != X1 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_441]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2624,plain,
% 3.87/0.99      ( X0 != k2_tmap_1(sK1,sK0,sK3,X1)
% 3.87/0.99      | X0 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X1))
% 3.87/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X1)) != k2_tmap_1(sK1,sK0,sK3,X1) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1842]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2812,plain,
% 3.87/0.99      ( k2_tmap_1(sK1,sK0,sK3,X0) != k2_tmap_1(sK1,sK0,sK3,X0)
% 3.87/0.99      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
% 3.87/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) != k2_tmap_1(sK1,sK0,sK3,X0) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2624]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2814,plain,
% 3.87/0.99      ( k2_tmap_1(sK1,sK0,sK3,sK1) != k2_tmap_1(sK1,sK0,sK3,sK1)
% 3.87/0.99      | k2_tmap_1(sK1,sK0,sK3,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
% 3.87/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) != k2_tmap_1(sK1,sK0,sK3,sK1) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2812]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2813,plain,
% 3.87/0.99      ( k2_tmap_1(sK1,sK0,sK3,X0) = k2_tmap_1(sK1,sK0,sK3,X0) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_440]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2815,plain,
% 3.87/0.99      ( k2_tmap_1(sK1,sK0,sK3,sK1) = k2_tmap_1(sK1,sK0,sK3,sK1) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2813]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_446,plain,
% 3.87/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.87/0.99      theory(equality) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1593,plain,
% 3.87/0.99      ( m1_subset_1(X0,X1)
% 3.87/0.99      | ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | X0 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2)
% 3.87/0.99      | X1 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_446]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1930,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | X0 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X1)
% 3.87/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1593]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4437,plain,
% 3.87/0.99      ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | k2_tmap_1(sK1,sK0,sK3,X0) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
% 3.87/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1930]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4443,plain,
% 3.87/0.99      ( k2_tmap_1(sK1,sK0,sK3,X0) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
% 3.87/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 3.87/0.99      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 3.87/0.99      | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_4437]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4445,plain,
% 3.87/0.99      ( k2_tmap_1(sK1,sK0,sK3,sK1) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
% 3.87/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 3.87/0.99      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 3.87/0.99      | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_4443]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7992,plain,
% 3.87/0.99      ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_5005,c_33,c_32,c_31,c_30,c_29,c_28,c_25,c_42,c_24,
% 3.87/0.99                 c_23,c_44,c_51,c_1555,c_1931,c_2407,c_2814,c_2815,
% 3.87/0.99                 c_4445]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4,plain,
% 3.87/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.87/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.87/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.87/0.99      | X2 = X3 ),
% 3.87/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1048,plain,
% 3.87/0.99      ( X0 = X1
% 3.87/0.99      | r2_relset_1(X2,X3,X0,X1) != iProver_top
% 3.87/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.87/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3531,plain,
% 3.87/0.99      ( sK3 = X0
% 3.87/0.99      | r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) != iProver_top
% 3.87/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1032,c_1048]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8001,plain,
% 3.87/0.99      ( k2_tmap_1(sK1,sK0,sK3,sK1) = sK3
% 3.87/0.99      | r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK1)) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_7992,c_3531]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_48,plain,
% 3.87/0.99      ( ~ m1_pre_topc(sK1,sK1)
% 3.87/0.99      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1))
% 3.87/0.99      | ~ l1_pre_topc(sK1)
% 3.87/0.99      | ~ v2_pre_topc(sK1) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1489,plain,
% 3.87/0.99      ( sK3 = sK3 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_440]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7,plain,
% 3.87/0.99      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3),X2)
% 3.87/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.87/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.87/0.99      | ~ r1_tarski(X0,X3)
% 3.87/0.99      | ~ v1_funct_1(X2) ),
% 3.87/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1416,plain,
% 3.87/0.99      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,sK3,X2),sK3)
% 3.87/0.99      | ~ v1_funct_2(sK3,X0,X1)
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.87/0.99      | ~ r1_tarski(X0,X2)
% 3.87/0.99      | ~ v1_funct_1(sK3) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1511,plain,
% 3.87/0.99      ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),sK3)
% 3.87/0.99      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | ~ r1_tarski(u1_struct_0(sK1),X0)
% 3.87/0.99      | ~ v1_funct_1(sK3) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1416]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1720,plain,
% 3.87/0.99      ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),sK3)
% 3.87/0.99      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1))
% 3.87/0.99      | ~ v1_funct_1(sK3) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1511]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1467,plain,
% 3.87/0.99      ( ~ r2_relset_1(X0,X1,X2,sK3)
% 3.87/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.87/0.99      | X2 = sK3 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1681,plain,
% 3.87/0.99      ( ~ r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK3)
% 3.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | X0 = sK3 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1467]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1782,plain,
% 3.87/0.99      ( ~ r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),sK3)
% 3.87/0.99      | ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = sK3 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1681]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1679,plain,
% 3.87/0.99      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_441]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2061,plain,
% 3.87/0.99      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1679]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2681,plain,
% 3.87/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) != sK3
% 3.87/0.99      | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
% 3.87/0.99      | sK3 != sK3 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2061]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1478,plain,
% 3.87/0.99      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_441]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4258,plain,
% 3.87/0.99      ( X0 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X1))
% 3.87/0.99      | X0 = sK3
% 3.87/0.99      | sK3 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X1)) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1478]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6125,plain,
% 3.87/0.99      ( k2_tmap_1(sK1,sK0,sK3,X0) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
% 3.87/0.99      | k2_tmap_1(sK1,sK0,sK3,X0) = sK3
% 3.87/0.99      | sK3 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_4258]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6126,plain,
% 3.87/0.99      ( k2_tmap_1(sK1,sK0,sK3,sK1) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
% 3.87/0.99      | k2_tmap_1(sK1,sK0,sK3,sK1) = sK3
% 3.87/0.99      | sK3 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_6125]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8321,plain,
% 3.87/0.99      ( k2_tmap_1(sK1,sK0,sK3,sK1) = sK3 ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_8001,c_33,c_32,c_31,c_30,c_29,c_28,c_25,c_24,c_23,
% 3.87/0.99                 c_48,c_51,c_1489,c_1555,c_1720,c_1782,c_2406,c_2681,
% 3.87/0.99                 c_2814,c_2815,c_6126]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8328,plain,
% 3.87/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = sK3 ),
% 3.87/0.99      inference(demodulation,[status(thm)],[c_8321,c_4862]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8518,plain,
% 3.87/0.99      ( k2_tmap_1(sK1,sK0,sK3,sK2) = sK3 ),
% 3.87/0.99      inference(light_normalisation,[status(thm)],[c_8503,c_8328]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_21,negated_conjecture,
% 3.87/0.99      ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
% 3.87/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1033,plain,
% 3.87/0.99      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8505,plain,
% 3.87/0.99      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) != iProver_top ),
% 3.87/0.99      inference(demodulation,[status(thm)],[c_8499,c_1033]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8519,plain,
% 3.87/0.99      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) != iProver_top ),
% 3.87/0.99      inference(demodulation,[status(thm)],[c_8518,c_8505]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_9,plain,
% 3.87/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1778,plain,
% 3.87/0.99      ( l1_struct_0(sK0) | ~ l1_pre_topc(sK0) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1779,plain,
% 3.87/0.99      ( l1_struct_0(sK0) = iProver_top
% 3.87/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1778]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_11,plain,
% 3.87/0.99      ( v2_struct_0(X0)
% 3.87/0.99      | ~ v1_xboole_0(u1_struct_0(X0))
% 3.87/0.99      | ~ l1_struct_0(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1711,plain,
% 3.87/0.99      ( v2_struct_0(sK0)
% 3.87/0.99      | ~ v1_xboole_0(u1_struct_0(sK0))
% 3.87/0.99      | ~ l1_struct_0(sK0) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1712,plain,
% 3.87/0.99      ( v2_struct_0(sK0) = iProver_top
% 3.87/0.99      | v1_xboole_0(u1_struct_0(sK0)) != iProver_top
% 3.87/0.99      | l1_struct_0(sK0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1711]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_15,plain,
% 3.87/0.99      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 3.87/0.99      | ~ v1_funct_2(X4,X2,X3)
% 3.87/0.99      | ~ v1_funct_2(X4,X0,X1)
% 3.87/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.87/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.87/0.99      | v1_xboole_0(X1)
% 3.87/0.99      | v1_xboole_0(X3)
% 3.87/0.99      | ~ v1_funct_1(X4) ),
% 3.87/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1421,plain,
% 3.87/0.99      ( r1_funct_2(X0,X1,X2,X3,sK3,sK3)
% 3.87/0.99      | ~ v1_funct_2(sK3,X0,X1)
% 3.87/0.99      | ~ v1_funct_2(sK3,X2,X3)
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.87/0.99      | v1_xboole_0(X1)
% 3.87/0.99      | v1_xboole_0(X3)
% 3.87/0.99      | ~ v1_funct_1(sK3) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1548,plain,
% 3.87/0.99      ( r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
% 3.87/0.99      | ~ v1_funct_2(sK3,X0,X1)
% 3.87/0.99      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | v1_xboole_0(X1)
% 3.87/0.99      | v1_xboole_0(u1_struct_0(sK0))
% 3.87/0.99      | ~ v1_funct_1(sK3) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1421]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1603,plain,
% 3.87/0.99      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
% 3.87/0.99      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.87/0.99      | v1_xboole_0(u1_struct_0(sK0))
% 3.87/0.99      | ~ v1_funct_1(sK3) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1548]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1604,plain,
% 3.87/0.99      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) = iProver_top
% 3.87/0.99      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.87/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.87/0.99      | v1_xboole_0(u1_struct_0(sK0)) = iProver_top
% 3.87/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1603]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(contradiction,plain,
% 3.87/0.99      ( $false ),
% 3.87/0.99      inference(minisat,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_8519,c_1779,c_1712,c_1604,c_44,c_43,c_42,c_36,c_34]) ).
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.87/0.99  
% 3.87/0.99  ------                               Statistics
% 3.87/0.99  
% 3.87/0.99  ------ Selected
% 3.87/0.99  
% 3.87/0.99  total_time:                             0.324
% 3.87/0.99  
%------------------------------------------------------------------------------
