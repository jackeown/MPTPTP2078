%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:28 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  198 (1904 expanded)
%              Number of clauses        :  115 ( 465 expanded)
%              Number of leaves         :   20 ( 487 expanded)
%              Depth                    :   28
%              Number of atoms          :  764 (12468 expanded)
%              Number of equality atoms :  172 ( 496 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f41])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f87,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f57])).

fof(f88,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f87])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
                <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_connsp_2(X2,X0,X1)
            | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
          & ( m1_connsp_2(X2,X0,X1)
            | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_connsp_2(sK3,X0,X1)
          | ~ m2_connsp_2(sK3,X0,k6_domain_1(u1_struct_0(X0),X1)) )
        & ( m1_connsp_2(sK3,X0,X1)
          | m2_connsp_2(sK3,X0,k6_domain_1(u1_struct_0(X0),X1)) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ m1_connsp_2(X2,X0,sK2)
              | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK2)) )
            & ( m1_connsp_2(X2,X0,sK2)
              | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK2)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_connsp_2(X2,X0,X1)
                  | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
                & ( m1_connsp_2(X2,X0,X1)
                  | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,sK1,X1)
                | ~ m2_connsp_2(X2,sK1,k6_domain_1(u1_struct_0(sK1),X1)) )
              & ( m1_connsp_2(X2,sK1,X1)
                | m2_connsp_2(X2,sK1,k6_domain_1(u1_struct_0(sK1),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ~ m1_connsp_2(sK3,sK1,sK2)
      | ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) )
    & ( m1_connsp_2(sK3,sK1,sK2)
      | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f50,f53,f52,f51])).

fof(f81,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f71,f61])).

fof(f78,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X2] :
          ( m2_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f84,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m2_connsp_2(X2,X0,X1)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f61])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_3,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1732,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1722,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1724,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3113,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1722,c_1724])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_59,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_62,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1890,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3705,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3113,c_28,c_26,c_25,c_59,c_62,c_1890])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_230,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_23,negated_conjecture,
    ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_234,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_235,plain,
    ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(renaming,[status(thm)],[c_234])).

cnf(c_17,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_20,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_170,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_20])).

cnf(c_171,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_170])).

cnf(c_431,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_171,c_28])).

cnf(c_432,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_436,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_27,c_26])).

cnf(c_774,plain,
    ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r2_hidden(X0,k1_tops_1(sK1,X1))
    | sK2 != X0
    | sK1 != sK1
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_235,c_436])).

cnf(c_775,plain,
    ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_774])).

cnf(c_777,plain,
    ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_775,c_25])).

cnf(c_19,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_21,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_164,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_21])).

cnf(c_165,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_164])).

cnf(c_512,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_165,c_26])).

cnf(c_513,plain,
    ( ~ m2_connsp_2(X0,sK1,X1)
    | r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ m2_connsp_2(X0,sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_513,c_27])).

cnf(c_518,plain,
    ( ~ m2_connsp_2(X0,sK1,X1)
    | r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_517])).

cnf(c_813,plain,
    ( r1_tarski(X0,k1_tops_1(sK1,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k6_domain_1(u1_struct_0(sK1),sK2) != X0
    | sK1 != sK1
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_777,c_518])).

cnf(c_814,plain,
    ( r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_813])).

cnf(c_896,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k1_tops_1(sK1,sK3) != X1
    | k6_domain_1(u1_struct_0(sK1),sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_230,c_814])).

cnf(c_897,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_896])).

cnf(c_1717,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_897])).

cnf(c_29,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_31,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_32,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_58,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_60,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_61,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_63,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_898,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_897])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1884,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1885,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1884])).

cnf(c_1950,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1717,c_29,c_31,c_32,c_60,c_63,c_898,c_1885])).

cnf(c_3710,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3705,c_1950])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_228,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_22,negated_conjecture,
    ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_232,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_233,plain,
    ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ m1_connsp_2(sK3,sK1,sK2) ),
    inference(renaming,[status(thm)],[c_232])).

cnf(c_16,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_473,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_28])).

cnf(c_474,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_478,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_474,c_27,c_26])).

cnf(c_788,plain,
    ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
    | sK2 != X0
    | sK1 != sK1
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_233,c_478])).

cnf(c_789,plain,
    ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_788])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_791,plain,
    ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_789,c_25,c_24])).

cnf(c_18,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_550,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_551,plain,
    ( m2_connsp_2(X0,sK1,X1)
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_550])).

cnf(c_555,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | m2_connsp_2(X0,sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_551,c_27])).

cnf(c_556,plain,
    ( m2_connsp_2(X0,sK1,X1)
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_555])).

cnf(c_826,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k6_domain_1(u1_struct_0(sK1),sK2) != X0
    | sK1 != sK1
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_791,c_556])).

cnf(c_827,plain,
    ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_826])).

cnf(c_829,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_827,c_24])).

cnf(c_830,plain,
    ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(renaming,[status(thm)],[c_829])).

cnf(c_865,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k1_tops_1(sK1,sK3) != X1
    | k6_domain_1(u1_struct_0(sK1),sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_228,c_830])).

cnf(c_866,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_865])).

cnf(c_1720,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_866])).

cnf(c_867,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_866])).

cnf(c_1943,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1720,c_29,c_31,c_32,c_60,c_63,c_867,c_1885])).

cnf(c_3711,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3705,c_1943])).

cnf(c_6,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2302,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2303,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2302])).

cnf(c_4107,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3711,c_2303])).

cnf(c_4538,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3710,c_2303,c_3711])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1727,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4545,plain,
    ( m1_subset_1(X0,k1_tops_1(sK1,sK3)) = iProver_top
    | r2_hidden(X0,k2_tarski(sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4538,c_1727])).

cnf(c_4936,plain,
    ( m1_subset_1(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_4545])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1728,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5782,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
    | v1_xboole_0(k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4936,c_1728])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_295,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_230])).

cnf(c_878,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,X1)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ v1_xboole_0(X2)
    | k1_tops_1(sK1,sK3) != X2
    | k6_domain_1(u1_struct_0(sK1),sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_295,c_814])).

cnf(c_879,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK1),sK2))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ v1_xboole_0(k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_878])).

cnf(c_1385,plain,
    ( ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_879])).

cnf(c_1719,plain,
    ( r2_hidden(X0,k6_domain_1(u1_struct_0(sK1),sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1385])).

cnf(c_3712,plain,
    ( r2_hidden(X0,k2_tarski(sK2,sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_3705,c_1719])).

cnf(c_3918,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_3712])).

cnf(c_1386,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ v1_xboole_0(k1_tops_1(sK1,sK3))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_879])).

cnf(c_1718,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
    | v1_xboole_0(k1_tops_1(sK1,sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1386])).

cnf(c_1407,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
    | v1_xboole_0(k1_tops_1(sK1,sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1386])).

cnf(c_2067,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
    | v1_xboole_0(k1_tops_1(sK1,sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1718,c_29,c_31,c_32,c_60,c_63,c_1407,c_1885])).

cnf(c_1729,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1726,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2382,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k2_tarski(X0,X0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_1726])).

cnf(c_2727,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_2382])).

cnf(c_2826,plain,
    ( v1_xboole_0(k1_tops_1(sK1,sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2067,c_2727])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5782,c_4107,c_3918,c_2826])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n010.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:15:44 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 3.02/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/0.97  
% 3.02/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.02/0.97  
% 3.02/0.97  ------  iProver source info
% 3.02/0.97  
% 3.02/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.02/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.02/0.97  git: non_committed_changes: false
% 3.02/0.97  git: last_make_outside_of_git: false
% 3.02/0.97  
% 3.02/0.97  ------ 
% 3.02/0.97  
% 3.02/0.97  ------ Input Options
% 3.02/0.97  
% 3.02/0.97  --out_options                           all
% 3.02/0.97  --tptp_safe_out                         true
% 3.02/0.97  --problem_path                          ""
% 3.02/0.97  --include_path                          ""
% 3.02/0.97  --clausifier                            res/vclausify_rel
% 3.02/0.97  --clausifier_options                    --mode clausify
% 3.02/0.97  --stdin                                 false
% 3.02/0.97  --stats_out                             all
% 3.02/0.97  
% 3.02/0.97  ------ General Options
% 3.02/0.97  
% 3.02/0.97  --fof                                   false
% 3.02/0.97  --time_out_real                         305.
% 3.02/0.97  --time_out_virtual                      -1.
% 3.02/0.97  --symbol_type_check                     false
% 3.02/0.97  --clausify_out                          false
% 3.02/0.97  --sig_cnt_out                           false
% 3.02/0.97  --trig_cnt_out                          false
% 3.02/0.97  --trig_cnt_out_tolerance                1.
% 3.02/0.97  --trig_cnt_out_sk_spl                   false
% 3.02/0.97  --abstr_cl_out                          false
% 3.02/0.97  
% 3.02/0.97  ------ Global Options
% 3.02/0.97  
% 3.02/0.97  --schedule                              default
% 3.02/0.97  --add_important_lit                     false
% 3.02/0.97  --prop_solver_per_cl                    1000
% 3.02/0.97  --min_unsat_core                        false
% 3.02/0.97  --soft_assumptions                      false
% 3.02/0.97  --soft_lemma_size                       3
% 3.02/0.97  --prop_impl_unit_size                   0
% 3.02/0.97  --prop_impl_unit                        []
% 3.02/0.97  --share_sel_clauses                     true
% 3.02/0.97  --reset_solvers                         false
% 3.02/0.97  --bc_imp_inh                            [conj_cone]
% 3.02/0.97  --conj_cone_tolerance                   3.
% 3.02/0.97  --extra_neg_conj                        none
% 3.02/0.97  --large_theory_mode                     true
% 3.02/0.97  --prolific_symb_bound                   200
% 3.02/0.97  --lt_threshold                          2000
% 3.02/0.97  --clause_weak_htbl                      true
% 3.02/0.97  --gc_record_bc_elim                     false
% 3.02/0.97  
% 3.02/0.97  ------ Preprocessing Options
% 3.02/0.97  
% 3.02/0.97  --preprocessing_flag                    true
% 3.02/0.97  --time_out_prep_mult                    0.1
% 3.02/0.97  --splitting_mode                        input
% 3.02/0.97  --splitting_grd                         true
% 3.02/0.97  --splitting_cvd                         false
% 3.02/0.97  --splitting_cvd_svl                     false
% 3.02/0.97  --splitting_nvd                         32
% 3.02/0.97  --sub_typing                            true
% 3.02/0.97  --prep_gs_sim                           true
% 3.02/0.97  --prep_unflatten                        true
% 3.02/0.97  --prep_res_sim                          true
% 3.02/0.97  --prep_upred                            true
% 3.02/0.97  --prep_sem_filter                       exhaustive
% 3.02/0.97  --prep_sem_filter_out                   false
% 3.02/0.97  --pred_elim                             true
% 3.02/0.97  --res_sim_input                         true
% 3.02/0.97  --eq_ax_congr_red                       true
% 3.02/0.97  --pure_diseq_elim                       true
% 3.02/0.97  --brand_transform                       false
% 3.02/0.97  --non_eq_to_eq                          false
% 3.02/0.97  --prep_def_merge                        true
% 3.02/0.97  --prep_def_merge_prop_impl              false
% 3.02/0.97  --prep_def_merge_mbd                    true
% 3.02/0.97  --prep_def_merge_tr_red                 false
% 3.02/0.97  --prep_def_merge_tr_cl                  false
% 3.02/0.97  --smt_preprocessing                     true
% 3.02/0.97  --smt_ac_axioms                         fast
% 3.02/0.97  --preprocessed_out                      false
% 3.02/0.97  --preprocessed_stats                    false
% 3.02/0.97  
% 3.02/0.97  ------ Abstraction refinement Options
% 3.02/0.97  
% 3.02/0.97  --abstr_ref                             []
% 3.02/0.97  --abstr_ref_prep                        false
% 3.02/0.97  --abstr_ref_until_sat                   false
% 3.02/0.97  --abstr_ref_sig_restrict                funpre
% 3.02/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/0.97  --abstr_ref_under                       []
% 3.02/0.97  
% 3.02/0.97  ------ SAT Options
% 3.02/0.97  
% 3.02/0.97  --sat_mode                              false
% 3.02/0.97  --sat_fm_restart_options                ""
% 3.02/0.97  --sat_gr_def                            false
% 3.02/0.97  --sat_epr_types                         true
% 3.02/0.97  --sat_non_cyclic_types                  false
% 3.02/0.97  --sat_finite_models                     false
% 3.02/0.97  --sat_fm_lemmas                         false
% 3.02/0.97  --sat_fm_prep                           false
% 3.02/0.97  --sat_fm_uc_incr                        true
% 3.02/0.97  --sat_out_model                         small
% 3.02/0.97  --sat_out_clauses                       false
% 3.02/0.97  
% 3.02/0.97  ------ QBF Options
% 3.02/0.97  
% 3.02/0.97  --qbf_mode                              false
% 3.02/0.97  --qbf_elim_univ                         false
% 3.02/0.97  --qbf_dom_inst                          none
% 3.02/0.97  --qbf_dom_pre_inst                      false
% 3.02/0.97  --qbf_sk_in                             false
% 3.02/0.97  --qbf_pred_elim                         true
% 3.02/0.97  --qbf_split                             512
% 3.02/0.97  
% 3.02/0.97  ------ BMC1 Options
% 3.02/0.97  
% 3.02/0.97  --bmc1_incremental                      false
% 3.02/0.97  --bmc1_axioms                           reachable_all
% 3.02/0.97  --bmc1_min_bound                        0
% 3.02/0.97  --bmc1_max_bound                        -1
% 3.02/0.97  --bmc1_max_bound_default                -1
% 3.02/0.97  --bmc1_symbol_reachability              true
% 3.02/0.97  --bmc1_property_lemmas                  false
% 3.02/0.97  --bmc1_k_induction                      false
% 3.02/0.97  --bmc1_non_equiv_states                 false
% 3.02/0.97  --bmc1_deadlock                         false
% 3.02/0.97  --bmc1_ucm                              false
% 3.02/0.97  --bmc1_add_unsat_core                   none
% 3.02/0.97  --bmc1_unsat_core_children              false
% 3.02/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/0.97  --bmc1_out_stat                         full
% 3.02/0.97  --bmc1_ground_init                      false
% 3.02/0.97  --bmc1_pre_inst_next_state              false
% 3.02/0.97  --bmc1_pre_inst_state                   false
% 3.02/0.97  --bmc1_pre_inst_reach_state             false
% 3.02/0.97  --bmc1_out_unsat_core                   false
% 3.02/0.97  --bmc1_aig_witness_out                  false
% 3.02/0.97  --bmc1_verbose                          false
% 3.02/0.97  --bmc1_dump_clauses_tptp                false
% 3.02/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.02/0.97  --bmc1_dump_file                        -
% 3.02/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.02/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.02/0.97  --bmc1_ucm_extend_mode                  1
% 3.02/0.97  --bmc1_ucm_init_mode                    2
% 3.02/0.97  --bmc1_ucm_cone_mode                    none
% 3.02/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.02/0.97  --bmc1_ucm_relax_model                  4
% 3.02/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.02/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/0.97  --bmc1_ucm_layered_model                none
% 3.02/0.97  --bmc1_ucm_max_lemma_size               10
% 3.02/0.97  
% 3.02/0.97  ------ AIG Options
% 3.02/0.97  
% 3.02/0.97  --aig_mode                              false
% 3.02/0.97  
% 3.02/0.97  ------ Instantiation Options
% 3.02/0.97  
% 3.02/0.97  --instantiation_flag                    true
% 3.02/0.97  --inst_sos_flag                         false
% 3.02/0.97  --inst_sos_phase                        true
% 3.02/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/0.97  --inst_lit_sel_side                     num_symb
% 3.02/0.97  --inst_solver_per_active                1400
% 3.02/0.97  --inst_solver_calls_frac                1.
% 3.02/0.97  --inst_passive_queue_type               priority_queues
% 3.02/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/0.97  --inst_passive_queues_freq              [25;2]
% 3.02/0.97  --inst_dismatching                      true
% 3.02/0.97  --inst_eager_unprocessed_to_passive     true
% 3.02/0.97  --inst_prop_sim_given                   true
% 3.02/0.97  --inst_prop_sim_new                     false
% 3.02/0.97  --inst_subs_new                         false
% 3.02/0.97  --inst_eq_res_simp                      false
% 3.02/0.97  --inst_subs_given                       false
% 3.02/0.97  --inst_orphan_elimination               true
% 3.02/0.97  --inst_learning_loop_flag               true
% 3.02/0.97  --inst_learning_start                   3000
% 3.02/0.97  --inst_learning_factor                  2
% 3.02/0.97  --inst_start_prop_sim_after_learn       3
% 3.02/0.97  --inst_sel_renew                        solver
% 3.02/0.97  --inst_lit_activity_flag                true
% 3.02/0.97  --inst_restr_to_given                   false
% 3.02/0.97  --inst_activity_threshold               500
% 3.02/0.97  --inst_out_proof                        true
% 3.02/0.97  
% 3.02/0.97  ------ Resolution Options
% 3.02/0.97  
% 3.02/0.97  --resolution_flag                       true
% 3.02/0.97  --res_lit_sel                           adaptive
% 3.02/0.97  --res_lit_sel_side                      none
% 3.02/0.97  --res_ordering                          kbo
% 3.02/0.97  --res_to_prop_solver                    active
% 3.02/0.97  --res_prop_simpl_new                    false
% 3.02/0.97  --res_prop_simpl_given                  true
% 3.02/0.97  --res_passive_queue_type                priority_queues
% 3.02/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/0.97  --res_passive_queues_freq               [15;5]
% 3.02/0.97  --res_forward_subs                      full
% 3.02/0.97  --res_backward_subs                     full
% 3.02/0.97  --res_forward_subs_resolution           true
% 3.02/0.97  --res_backward_subs_resolution          true
% 3.02/0.97  --res_orphan_elimination                true
% 3.02/0.97  --res_time_limit                        2.
% 3.02/0.97  --res_out_proof                         true
% 3.02/0.97  
% 3.02/0.97  ------ Superposition Options
% 3.02/0.97  
% 3.02/0.97  --superposition_flag                    true
% 3.02/0.97  --sup_passive_queue_type                priority_queues
% 3.02/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.02/0.97  --demod_completeness_check              fast
% 3.02/0.97  --demod_use_ground                      true
% 3.02/0.97  --sup_to_prop_solver                    passive
% 3.02/0.97  --sup_prop_simpl_new                    true
% 3.02/0.97  --sup_prop_simpl_given                  true
% 3.02/0.97  --sup_fun_splitting                     false
% 3.02/0.97  --sup_smt_interval                      50000
% 3.02/0.97  
% 3.02/0.97  ------ Superposition Simplification Setup
% 3.02/0.97  
% 3.02/0.97  --sup_indices_passive                   []
% 3.02/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.97  --sup_full_bw                           [BwDemod]
% 3.02/0.97  --sup_immed_triv                        [TrivRules]
% 3.02/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.97  --sup_immed_bw_main                     []
% 3.02/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.97  
% 3.02/0.97  ------ Combination Options
% 3.02/0.97  
% 3.02/0.97  --comb_res_mult                         3
% 3.02/0.97  --comb_sup_mult                         2
% 3.02/0.97  --comb_inst_mult                        10
% 3.02/0.97  
% 3.02/0.97  ------ Debug Options
% 3.02/0.97  
% 3.02/0.97  --dbg_backtrace                         false
% 3.02/0.97  --dbg_dump_prop_clauses                 false
% 3.02/0.97  --dbg_dump_prop_clauses_file            -
% 3.02/0.97  --dbg_out_stat                          false
% 3.02/0.97  ------ Parsing...
% 3.02/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.02/0.97  
% 3.02/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.02/0.97  
% 3.02/0.97  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.02/0.97  
% 3.02/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.02/0.97  ------ Proving...
% 3.02/0.97  ------ Problem Properties 
% 3.02/0.97  
% 3.02/0.97  
% 3.02/0.97  clauses                                 19
% 3.02/0.97  conjectures                             2
% 3.02/0.97  EPR                                     1
% 3.02/0.97  Horn                                    12
% 3.02/0.97  unary                                   5
% 3.02/0.97  binary                                  2
% 3.02/0.97  lits                                    47
% 3.02/0.97  lits eq                                 10
% 3.02/0.97  fd_pure                                 0
% 3.02/0.97  fd_pseudo                               0
% 3.02/0.97  fd_cond                                 0
% 3.02/0.97  fd_pseudo_cond                          3
% 3.02/0.97  AC symbols                              0
% 3.02/0.97  
% 3.02/0.97  ------ Schedule dynamic 5 is on 
% 3.02/0.97  
% 3.02/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.02/0.97  
% 3.02/0.97  
% 3.02/0.97  ------ 
% 3.02/0.97  Current options:
% 3.02/0.97  ------ 
% 3.02/0.97  
% 3.02/0.97  ------ Input Options
% 3.02/0.97  
% 3.02/0.97  --out_options                           all
% 3.02/0.97  --tptp_safe_out                         true
% 3.02/0.97  --problem_path                          ""
% 3.02/0.97  --include_path                          ""
% 3.02/0.97  --clausifier                            res/vclausify_rel
% 3.02/0.97  --clausifier_options                    --mode clausify
% 3.02/0.97  --stdin                                 false
% 3.02/0.97  --stats_out                             all
% 3.02/0.97  
% 3.02/0.97  ------ General Options
% 3.02/0.97  
% 3.02/0.97  --fof                                   false
% 3.02/0.97  --time_out_real                         305.
% 3.02/0.97  --time_out_virtual                      -1.
% 3.02/0.97  --symbol_type_check                     false
% 3.02/0.97  --clausify_out                          false
% 3.02/0.97  --sig_cnt_out                           false
% 3.02/0.97  --trig_cnt_out                          false
% 3.02/0.97  --trig_cnt_out_tolerance                1.
% 3.02/0.97  --trig_cnt_out_sk_spl                   false
% 3.02/0.97  --abstr_cl_out                          false
% 3.02/0.97  
% 3.02/0.97  ------ Global Options
% 3.02/0.97  
% 3.02/0.97  --schedule                              default
% 3.02/0.97  --add_important_lit                     false
% 3.02/0.97  --prop_solver_per_cl                    1000
% 3.02/0.97  --min_unsat_core                        false
% 3.02/0.97  --soft_assumptions                      false
% 3.02/0.97  --soft_lemma_size                       3
% 3.02/0.97  --prop_impl_unit_size                   0
% 3.02/0.97  --prop_impl_unit                        []
% 3.02/0.97  --share_sel_clauses                     true
% 3.02/0.97  --reset_solvers                         false
% 3.02/0.97  --bc_imp_inh                            [conj_cone]
% 3.02/0.97  --conj_cone_tolerance                   3.
% 3.02/0.97  --extra_neg_conj                        none
% 3.02/0.97  --large_theory_mode                     true
% 3.02/0.97  --prolific_symb_bound                   200
% 3.02/0.97  --lt_threshold                          2000
% 3.02/0.97  --clause_weak_htbl                      true
% 3.02/0.97  --gc_record_bc_elim                     false
% 3.02/0.97  
% 3.02/0.97  ------ Preprocessing Options
% 3.02/0.97  
% 3.02/0.97  --preprocessing_flag                    true
% 3.02/0.97  --time_out_prep_mult                    0.1
% 3.02/0.97  --splitting_mode                        input
% 3.02/0.97  --splitting_grd                         true
% 3.02/0.97  --splitting_cvd                         false
% 3.02/0.97  --splitting_cvd_svl                     false
% 3.02/0.97  --splitting_nvd                         32
% 3.02/0.97  --sub_typing                            true
% 3.02/0.97  --prep_gs_sim                           true
% 3.02/0.97  --prep_unflatten                        true
% 3.02/0.97  --prep_res_sim                          true
% 3.02/0.97  --prep_upred                            true
% 3.02/0.97  --prep_sem_filter                       exhaustive
% 3.02/0.97  --prep_sem_filter_out                   false
% 3.02/0.97  --pred_elim                             true
% 3.02/0.97  --res_sim_input                         true
% 3.02/0.97  --eq_ax_congr_red                       true
% 3.02/0.97  --pure_diseq_elim                       true
% 3.02/0.97  --brand_transform                       false
% 3.02/0.97  --non_eq_to_eq                          false
% 3.02/0.97  --prep_def_merge                        true
% 3.02/0.97  --prep_def_merge_prop_impl              false
% 3.02/0.97  --prep_def_merge_mbd                    true
% 3.02/0.97  --prep_def_merge_tr_red                 false
% 3.02/0.97  --prep_def_merge_tr_cl                  false
% 3.02/0.97  --smt_preprocessing                     true
% 3.02/0.97  --smt_ac_axioms                         fast
% 3.02/0.97  --preprocessed_out                      false
% 3.02/0.97  --preprocessed_stats                    false
% 3.02/0.97  
% 3.02/0.97  ------ Abstraction refinement Options
% 3.02/0.97  
% 3.02/0.97  --abstr_ref                             []
% 3.02/0.97  --abstr_ref_prep                        false
% 3.02/0.97  --abstr_ref_until_sat                   false
% 3.02/0.97  --abstr_ref_sig_restrict                funpre
% 3.02/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/0.97  --abstr_ref_under                       []
% 3.02/0.97  
% 3.02/0.97  ------ SAT Options
% 3.02/0.97  
% 3.02/0.97  --sat_mode                              false
% 3.02/0.97  --sat_fm_restart_options                ""
% 3.02/0.97  --sat_gr_def                            false
% 3.02/0.97  --sat_epr_types                         true
% 3.02/0.97  --sat_non_cyclic_types                  false
% 3.02/0.97  --sat_finite_models                     false
% 3.02/0.97  --sat_fm_lemmas                         false
% 3.02/0.97  --sat_fm_prep                           false
% 3.02/0.97  --sat_fm_uc_incr                        true
% 3.02/0.97  --sat_out_model                         small
% 3.02/0.97  --sat_out_clauses                       false
% 3.02/0.97  
% 3.02/0.97  ------ QBF Options
% 3.02/0.97  
% 3.02/0.97  --qbf_mode                              false
% 3.02/0.97  --qbf_elim_univ                         false
% 3.02/0.97  --qbf_dom_inst                          none
% 3.02/0.97  --qbf_dom_pre_inst                      false
% 3.02/0.97  --qbf_sk_in                             false
% 3.02/0.97  --qbf_pred_elim                         true
% 3.02/0.97  --qbf_split                             512
% 3.02/0.97  
% 3.02/0.97  ------ BMC1 Options
% 3.02/0.97  
% 3.02/0.97  --bmc1_incremental                      false
% 3.02/0.97  --bmc1_axioms                           reachable_all
% 3.02/0.97  --bmc1_min_bound                        0
% 3.02/0.97  --bmc1_max_bound                        -1
% 3.02/0.97  --bmc1_max_bound_default                -1
% 3.02/0.97  --bmc1_symbol_reachability              true
% 3.02/0.97  --bmc1_property_lemmas                  false
% 3.02/0.97  --bmc1_k_induction                      false
% 3.02/0.97  --bmc1_non_equiv_states                 false
% 3.02/0.97  --bmc1_deadlock                         false
% 3.02/0.97  --bmc1_ucm                              false
% 3.02/0.97  --bmc1_add_unsat_core                   none
% 3.02/0.97  --bmc1_unsat_core_children              false
% 3.02/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/0.97  --bmc1_out_stat                         full
% 3.02/0.97  --bmc1_ground_init                      false
% 3.02/0.97  --bmc1_pre_inst_next_state              false
% 3.02/0.97  --bmc1_pre_inst_state                   false
% 3.02/0.97  --bmc1_pre_inst_reach_state             false
% 3.02/0.97  --bmc1_out_unsat_core                   false
% 3.02/0.97  --bmc1_aig_witness_out                  false
% 3.02/0.97  --bmc1_verbose                          false
% 3.02/0.97  --bmc1_dump_clauses_tptp                false
% 3.02/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.02/0.97  --bmc1_dump_file                        -
% 3.02/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.02/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.02/0.97  --bmc1_ucm_extend_mode                  1
% 3.02/0.97  --bmc1_ucm_init_mode                    2
% 3.02/0.97  --bmc1_ucm_cone_mode                    none
% 3.02/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.02/0.97  --bmc1_ucm_relax_model                  4
% 3.02/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.02/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/0.97  --bmc1_ucm_layered_model                none
% 3.02/0.97  --bmc1_ucm_max_lemma_size               10
% 3.02/0.97  
% 3.02/0.97  ------ AIG Options
% 3.02/0.97  
% 3.02/0.97  --aig_mode                              false
% 3.02/0.97  
% 3.02/0.97  ------ Instantiation Options
% 3.02/0.97  
% 3.02/0.97  --instantiation_flag                    true
% 3.02/0.97  --inst_sos_flag                         false
% 3.02/0.97  --inst_sos_phase                        true
% 3.02/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/0.97  --inst_lit_sel_side                     none
% 3.02/0.97  --inst_solver_per_active                1400
% 3.02/0.97  --inst_solver_calls_frac                1.
% 3.02/0.97  --inst_passive_queue_type               priority_queues
% 3.02/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/0.97  --inst_passive_queues_freq              [25;2]
% 3.02/0.97  --inst_dismatching                      true
% 3.02/0.97  --inst_eager_unprocessed_to_passive     true
% 3.02/0.97  --inst_prop_sim_given                   true
% 3.02/0.97  --inst_prop_sim_new                     false
% 3.02/0.97  --inst_subs_new                         false
% 3.02/0.97  --inst_eq_res_simp                      false
% 3.02/0.97  --inst_subs_given                       false
% 3.02/0.97  --inst_orphan_elimination               true
% 3.02/0.97  --inst_learning_loop_flag               true
% 3.02/0.97  --inst_learning_start                   3000
% 3.02/0.97  --inst_learning_factor                  2
% 3.02/0.97  --inst_start_prop_sim_after_learn       3
% 3.02/0.97  --inst_sel_renew                        solver
% 3.02/0.97  --inst_lit_activity_flag                true
% 3.02/0.97  --inst_restr_to_given                   false
% 3.02/0.97  --inst_activity_threshold               500
% 3.02/0.97  --inst_out_proof                        true
% 3.02/0.97  
% 3.02/0.97  ------ Resolution Options
% 3.02/0.97  
% 3.02/0.97  --resolution_flag                       false
% 3.02/0.97  --res_lit_sel                           adaptive
% 3.02/0.97  --res_lit_sel_side                      none
% 3.02/0.97  --res_ordering                          kbo
% 3.02/0.97  --res_to_prop_solver                    active
% 3.02/0.97  --res_prop_simpl_new                    false
% 3.02/0.97  --res_prop_simpl_given                  true
% 3.02/0.97  --res_passive_queue_type                priority_queues
% 3.02/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/0.97  --res_passive_queues_freq               [15;5]
% 3.02/0.97  --res_forward_subs                      full
% 3.02/0.97  --res_backward_subs                     full
% 3.02/0.97  --res_forward_subs_resolution           true
% 3.02/0.97  --res_backward_subs_resolution          true
% 3.02/0.97  --res_orphan_elimination                true
% 3.02/0.97  --res_time_limit                        2.
% 3.02/0.97  --res_out_proof                         true
% 3.02/0.97  
% 3.02/0.97  ------ Superposition Options
% 3.02/0.97  
% 3.02/0.97  --superposition_flag                    true
% 3.02/0.97  --sup_passive_queue_type                priority_queues
% 3.02/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.02/0.97  --demod_completeness_check              fast
% 3.02/0.97  --demod_use_ground                      true
% 3.02/0.97  --sup_to_prop_solver                    passive
% 3.02/0.97  --sup_prop_simpl_new                    true
% 3.02/0.97  --sup_prop_simpl_given                  true
% 3.02/0.97  --sup_fun_splitting                     false
% 3.02/0.97  --sup_smt_interval                      50000
% 3.02/0.97  
% 3.02/0.97  ------ Superposition Simplification Setup
% 3.02/0.97  
% 3.02/0.97  --sup_indices_passive                   []
% 3.02/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.97  --sup_full_bw                           [BwDemod]
% 3.02/0.97  --sup_immed_triv                        [TrivRules]
% 3.02/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.97  --sup_immed_bw_main                     []
% 3.02/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.97  
% 3.02/0.97  ------ Combination Options
% 3.02/0.97  
% 3.02/0.97  --comb_res_mult                         3
% 3.02/0.97  --comb_sup_mult                         2
% 3.02/0.97  --comb_inst_mult                        10
% 3.02/0.97  
% 3.02/0.97  ------ Debug Options
% 3.02/0.97  
% 3.02/0.97  --dbg_backtrace                         false
% 3.02/0.97  --dbg_dump_prop_clauses                 false
% 3.02/0.97  --dbg_dump_prop_clauses_file            -
% 3.02/0.97  --dbg_out_stat                          false
% 3.02/0.97  
% 3.02/0.97  
% 3.02/0.97  
% 3.02/0.97  
% 3.02/0.97  ------ Proving...
% 3.02/0.97  
% 3.02/0.97  
% 3.02/0.97  % SZS status Theorem for theBenchmark.p
% 3.02/0.97  
% 3.02/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.02/0.97  
% 3.02/0.97  fof(f1,axiom,(
% 3.02/0.97    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.02/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.97  
% 3.02/0.97  fof(f41,plain,(
% 3.02/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.02/0.97    inference(nnf_transformation,[],[f1])).
% 3.02/0.97  
% 3.02/0.97  fof(f42,plain,(
% 3.02/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.02/0.97    inference(flattening,[],[f41])).
% 3.02/0.97  
% 3.02/0.97  fof(f43,plain,(
% 3.02/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.02/0.97    inference(rectify,[],[f42])).
% 3.02/0.97  
% 3.02/0.97  fof(f44,plain,(
% 3.02/0.97    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.02/0.97    introduced(choice_axiom,[])).
% 3.02/0.97  
% 3.02/0.97  fof(f45,plain,(
% 3.02/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.02/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 3.02/0.97  
% 3.02/0.97  fof(f57,plain,(
% 3.02/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.02/0.97    inference(cnf_transformation,[],[f45])).
% 3.02/0.97  
% 3.02/0.97  fof(f87,plain,(
% 3.02/0.97    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 3.02/0.97    inference(equality_resolution,[],[f57])).
% 3.02/0.97  
% 3.02/0.97  fof(f88,plain,(
% 3.02/0.97    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 3.02/0.97    inference(equality_resolution,[],[f87])).
% 3.02/0.97  
% 3.02/0.97  fof(f16,conjecture,(
% 3.02/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 3.02/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.97  
% 3.02/0.97  fof(f17,negated_conjecture,(
% 3.02/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 3.02/0.97    inference(negated_conjecture,[],[f16])).
% 3.02/0.97  
% 3.02/0.97  fof(f39,plain,(
% 3.02/0.97    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.02/0.97    inference(ennf_transformation,[],[f17])).
% 3.02/0.97  
% 3.02/0.97  fof(f40,plain,(
% 3.02/0.97    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.02/0.97    inference(flattening,[],[f39])).
% 3.02/0.97  
% 3.02/0.97  fof(f49,plain,(
% 3.02/0.97    ? [X0] : (? [X1] : (? [X2] : (((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.02/0.97    inference(nnf_transformation,[],[f40])).
% 3.02/0.97  
% 3.02/0.97  fof(f50,plain,(
% 3.02/0.97    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.02/0.98    inference(flattening,[],[f49])).
% 3.02/0.98  
% 3.02/0.98  fof(f53,plain,(
% 3.02/0.98    ( ! [X0,X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((~m1_connsp_2(sK3,X0,X1) | ~m2_connsp_2(sK3,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(sK3,X0,X1) | m2_connsp_2(sK3,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.02/0.98    introduced(choice_axiom,[])).
% 3.02/0.98  
% 3.02/0.98  fof(f52,plain,(
% 3.02/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~m1_connsp_2(X2,X0,sK2) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK2))) & (m1_connsp_2(X2,X0,sK2) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 3.02/0.98    introduced(choice_axiom,[])).
% 3.02/0.98  
% 3.02/0.98  fof(f51,plain,(
% 3.02/0.98    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK1,X1) | ~m2_connsp_2(X2,sK1,k6_domain_1(u1_struct_0(sK1),X1))) & (m1_connsp_2(X2,sK1,X1) | m2_connsp_2(X2,sK1,k6_domain_1(u1_struct_0(sK1),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.02/0.98    introduced(choice_axiom,[])).
% 3.02/0.98  
% 3.02/0.98  fof(f54,plain,(
% 3.02/0.98    (((~m1_connsp_2(sK3,sK1,sK2) | ~m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))) & (m1_connsp_2(sK3,sK1,sK2) | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.02/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f50,f53,f52,f51])).
% 3.02/0.98  
% 3.02/0.98  fof(f81,plain,(
% 3.02/0.98    m1_subset_1(sK2,u1_struct_0(sK1))),
% 3.02/0.98    inference(cnf_transformation,[],[f54])).
% 3.02/0.98  
% 3.02/0.98  fof(f11,axiom,(
% 3.02/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f29,plain,(
% 3.02/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.02/0.98    inference(ennf_transformation,[],[f11])).
% 3.02/0.98  
% 3.02/0.98  fof(f30,plain,(
% 3.02/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.02/0.98    inference(flattening,[],[f29])).
% 3.02/0.98  
% 3.02/0.98  fof(f71,plain,(
% 3.02/0.98    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f30])).
% 3.02/0.98  
% 3.02/0.98  fof(f2,axiom,(
% 3.02/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f61,plain,(
% 3.02/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f2])).
% 3.02/0.98  
% 3.02/0.98  fof(f86,plain,(
% 3.02/0.98    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.02/0.98    inference(definition_unfolding,[],[f71,f61])).
% 3.02/0.98  
% 3.02/0.98  fof(f78,plain,(
% 3.02/0.98    ~v2_struct_0(sK1)),
% 3.02/0.98    inference(cnf_transformation,[],[f54])).
% 3.02/0.98  
% 3.02/0.98  fof(f80,plain,(
% 3.02/0.98    l1_pre_topc(sK1)),
% 3.02/0.98    inference(cnf_transformation,[],[f54])).
% 3.02/0.98  
% 3.02/0.98  fof(f9,axiom,(
% 3.02/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f25,plain,(
% 3.02/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.02/0.98    inference(ennf_transformation,[],[f9])).
% 3.02/0.98  
% 3.02/0.98  fof(f26,plain,(
% 3.02/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.02/0.98    inference(flattening,[],[f25])).
% 3.02/0.98  
% 3.02/0.98  fof(f69,plain,(
% 3.02/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f26])).
% 3.02/0.98  
% 3.02/0.98  fof(f8,axiom,(
% 3.02/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f24,plain,(
% 3.02/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.02/0.98    inference(ennf_transformation,[],[f8])).
% 3.02/0.98  
% 3.02/0.98  fof(f68,plain,(
% 3.02/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f24])).
% 3.02/0.98  
% 3.02/0.98  fof(f5,axiom,(
% 3.02/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f46,plain,(
% 3.02/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.02/0.98    inference(nnf_transformation,[],[f5])).
% 3.02/0.98  
% 3.02/0.98  fof(f65,plain,(
% 3.02/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f46])).
% 3.02/0.98  
% 3.02/0.98  fof(f83,plain,(
% 3.02/0.98    m1_connsp_2(sK3,sK1,sK2) | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))),
% 3.02/0.98    inference(cnf_transformation,[],[f54])).
% 3.02/0.98  
% 3.02/0.98  fof(f12,axiom,(
% 3.02/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 3.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f31,plain,(
% 3.02/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.02/0.98    inference(ennf_transformation,[],[f12])).
% 3.02/0.98  
% 3.02/0.98  fof(f32,plain,(
% 3.02/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/0.98    inference(flattening,[],[f31])).
% 3.02/0.98  
% 3.02/0.98  fof(f47,plain,(
% 3.02/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/0.98    inference(nnf_transformation,[],[f32])).
% 3.02/0.98  
% 3.02/0.98  fof(f72,plain,(
% 3.02/0.98    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f47])).
% 3.02/0.98  
% 3.02/0.98  fof(f14,axiom,(
% 3.02/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f35,plain,(
% 3.02/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.02/0.98    inference(ennf_transformation,[],[f14])).
% 3.02/0.98  
% 3.02/0.98  fof(f36,plain,(
% 3.02/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/0.98    inference(flattening,[],[f35])).
% 3.02/0.98  
% 3.02/0.98  fof(f76,plain,(
% 3.02/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f36])).
% 3.02/0.98  
% 3.02/0.98  fof(f79,plain,(
% 3.02/0.98    v2_pre_topc(sK1)),
% 3.02/0.98    inference(cnf_transformation,[],[f54])).
% 3.02/0.98  
% 3.02/0.98  fof(f13,axiom,(
% 3.02/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 3.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f33,plain,(
% 3.02/0.98    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.02/0.98    inference(ennf_transformation,[],[f13])).
% 3.02/0.98  
% 3.02/0.98  fof(f34,plain,(
% 3.02/0.98    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.02/0.98    inference(flattening,[],[f33])).
% 3.02/0.98  
% 3.02/0.98  fof(f48,plain,(
% 3.02/0.98    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.02/0.98    inference(nnf_transformation,[],[f34])).
% 3.02/0.98  
% 3.02/0.98  fof(f74,plain,(
% 3.02/0.98    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f48])).
% 3.02/0.98  
% 3.02/0.98  fof(f15,axiom,(
% 3.02/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X2] : (m2_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f37,plain,(
% 3.02/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.02/0.98    inference(ennf_transformation,[],[f15])).
% 3.02/0.98  
% 3.02/0.98  fof(f38,plain,(
% 3.02/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.02/0.98    inference(flattening,[],[f37])).
% 3.02/0.98  
% 3.02/0.98  fof(f77,plain,(
% 3.02/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f38])).
% 3.02/0.98  
% 3.02/0.98  fof(f10,axiom,(
% 3.02/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f27,plain,(
% 3.02/0.98    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.02/0.98    inference(ennf_transformation,[],[f10])).
% 3.02/0.98  
% 3.02/0.98  fof(f28,plain,(
% 3.02/0.98    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.02/0.98    inference(flattening,[],[f27])).
% 3.02/0.98  
% 3.02/0.98  fof(f70,plain,(
% 3.02/0.98    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f28])).
% 3.02/0.98  
% 3.02/0.98  fof(f64,plain,(
% 3.02/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.02/0.98    inference(cnf_transformation,[],[f46])).
% 3.02/0.98  
% 3.02/0.98  fof(f84,plain,(
% 3.02/0.98    ~m1_connsp_2(sK3,sK1,sK2) | ~m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))),
% 3.02/0.98    inference(cnf_transformation,[],[f54])).
% 3.02/0.98  
% 3.02/0.98  fof(f73,plain,(
% 3.02/0.98    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f47])).
% 3.02/0.98  
% 3.02/0.98  fof(f82,plain,(
% 3.02/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.02/0.98    inference(cnf_transformation,[],[f54])).
% 3.02/0.98  
% 3.02/0.98  fof(f75,plain,(
% 3.02/0.98    ( ! [X2,X0,X1] : (m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f48])).
% 3.02/0.98  
% 3.02/0.98  fof(f3,axiom,(
% 3.02/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 3.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f18,plain,(
% 3.02/0.98    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 3.02/0.98    inference(ennf_transformation,[],[f3])).
% 3.02/0.98  
% 3.02/0.98  fof(f62,plain,(
% 3.02/0.98    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f18])).
% 3.02/0.98  
% 3.02/0.98  fof(f85,plain,(
% 3.02/0.98    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.02/0.98    inference(definition_unfolding,[],[f62,f61])).
% 3.02/0.98  
% 3.02/0.98  fof(f6,axiom,(
% 3.02/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f21,plain,(
% 3.02/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.02/0.98    inference(ennf_transformation,[],[f6])).
% 3.02/0.98  
% 3.02/0.98  fof(f22,plain,(
% 3.02/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.02/0.98    inference(flattening,[],[f21])).
% 3.02/0.98  
% 3.02/0.98  fof(f66,plain,(
% 3.02/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f22])).
% 3.02/0.98  
% 3.02/0.98  fof(f4,axiom,(
% 3.02/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f19,plain,(
% 3.02/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.02/0.98    inference(ennf_transformation,[],[f4])).
% 3.02/0.98  
% 3.02/0.98  fof(f20,plain,(
% 3.02/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.02/0.98    inference(flattening,[],[f19])).
% 3.02/0.98  
% 3.02/0.98  fof(f63,plain,(
% 3.02/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f20])).
% 3.02/0.98  
% 3.02/0.98  fof(f7,axiom,(
% 3.02/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f23,plain,(
% 3.02/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.02/0.98    inference(ennf_transformation,[],[f7])).
% 3.02/0.98  
% 3.02/0.98  fof(f67,plain,(
% 3.02/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f23])).
% 3.02/0.98  
% 3.02/0.98  cnf(c_3,plain,
% 3.02/0.98      ( r2_hidden(X0,k2_tarski(X1,X0)) ),
% 3.02/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1732,plain,
% 3.02/0.98      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_25,negated_conjecture,
% 3.02/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 3.02/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1722,plain,
% 3.02/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_15,plain,
% 3.02/0.98      ( ~ m1_subset_1(X0,X1)
% 3.02/0.98      | v1_xboole_0(X1)
% 3.02/0.98      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 3.02/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1724,plain,
% 3.02/0.98      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 3.02/0.98      | m1_subset_1(X1,X0) != iProver_top
% 3.02/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_3113,plain,
% 3.02/0.98      ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
% 3.02/0.98      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 3.02/0.98      inference(superposition,[status(thm)],[c_1722,c_1724]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_28,negated_conjecture,
% 3.02/0.98      ( ~ v2_struct_0(sK1) ),
% 3.02/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_26,negated_conjecture,
% 3.02/0.98      ( l1_pre_topc(sK1) ),
% 3.02/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_13,plain,
% 3.02/0.98      ( v2_struct_0(X0)
% 3.02/0.98      | ~ l1_struct_0(X0)
% 3.02/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.02/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_59,plain,
% 3.02/0.98      ( v2_struct_0(sK1)
% 3.02/0.98      | ~ l1_struct_0(sK1)
% 3.02/0.98      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.02/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_12,plain,
% 3.02/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.02/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_62,plain,
% 3.02/0.98      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 3.02/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1890,plain,
% 3.02/0.98      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.02/0.98      | v1_xboole_0(u1_struct_0(sK1))
% 3.02/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
% 3.02/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_3705,plain,
% 3.02/0.98      ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
% 3.02/0.98      inference(global_propositional_subsumption,
% 3.02/0.98                [status(thm)],
% 3.02/0.98                [c_3113,c_28,c_26,c_25,c_59,c_62,c_1890]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_8,plain,
% 3.02/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.02/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_230,plain,
% 3.02/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.02/0.98      inference(prop_impl,[status(thm)],[c_8]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_23,negated_conjecture,
% 3.02/0.98      ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 3.02/0.98      | m1_connsp_2(sK3,sK1,sK2) ),
% 3.02/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_234,plain,
% 3.02/0.98      ( m1_connsp_2(sK3,sK1,sK2)
% 3.02/0.98      | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
% 3.02/0.98      inference(prop_impl,[status(thm)],[c_23]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_235,plain,
% 3.02/0.98      ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 3.02/0.98      | m1_connsp_2(sK3,sK1,sK2) ),
% 3.02/0.98      inference(renaming,[status(thm)],[c_234]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_17,plain,
% 3.02/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.02/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.02/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.02/0.98      | ~ v2_pre_topc(X1)
% 3.02/0.98      | v2_struct_0(X1)
% 3.02/0.98      | ~ l1_pre_topc(X1) ),
% 3.02/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_20,plain,
% 3.02/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.02/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.02/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.98      | ~ v2_pre_topc(X1)
% 3.02/0.98      | v2_struct_0(X1)
% 3.02/0.98      | ~ l1_pre_topc(X1) ),
% 3.02/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_170,plain,
% 3.02/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.02/0.98      | ~ m1_connsp_2(X0,X1,X2)
% 3.02/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.02/0.98      | ~ v2_pre_topc(X1)
% 3.02/0.98      | v2_struct_0(X1)
% 3.02/0.98      | ~ l1_pre_topc(X1) ),
% 3.02/0.98      inference(global_propositional_subsumption,
% 3.02/0.98                [status(thm)],
% 3.02/0.98                [c_17,c_20]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_171,plain,
% 3.02/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.02/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.02/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.02/0.98      | ~ v2_pre_topc(X1)
% 3.02/0.98      | v2_struct_0(X1)
% 3.02/0.98      | ~ l1_pre_topc(X1) ),
% 3.02/0.98      inference(renaming,[status(thm)],[c_170]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_431,plain,
% 3.02/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.02/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.02/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.02/0.98      | ~ v2_pre_topc(X1)
% 3.02/0.98      | ~ l1_pre_topc(X1)
% 3.02/0.98      | sK1 != X1 ),
% 3.02/0.98      inference(resolution_lifted,[status(thm)],[c_171,c_28]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_432,plain,
% 3.02/0.98      ( ~ m1_connsp_2(X0,sK1,X1)
% 3.02/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.02/0.98      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 3.02/0.98      | ~ v2_pre_topc(sK1)
% 3.02/0.98      | ~ l1_pre_topc(sK1) ),
% 3.02/0.98      inference(unflattening,[status(thm)],[c_431]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_27,negated_conjecture,
% 3.02/0.98      ( v2_pre_topc(sK1) ),
% 3.02/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_436,plain,
% 3.02/0.98      ( ~ m1_connsp_2(X0,sK1,X1)
% 3.02/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.02/0.98      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 3.02/0.98      inference(global_propositional_subsumption,
% 3.02/0.98                [status(thm)],
% 3.02/0.98                [c_432,c_27,c_26]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_774,plain,
% 3.02/0.98      ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 3.02/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.02/0.98      | r2_hidden(X0,k1_tops_1(sK1,X1))
% 3.02/0.98      | sK2 != X0
% 3.02/0.98      | sK1 != sK1
% 3.02/0.98      | sK3 != X1 ),
% 3.02/0.98      inference(resolution_lifted,[status(thm)],[c_235,c_436]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_775,plain,
% 3.02/0.98      ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 3.02/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 3.02/0.98      inference(unflattening,[status(thm)],[c_774]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_777,plain,
% 3.02/0.98      ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 3.02/0.98      inference(global_propositional_subsumption,
% 3.02/0.98                [status(thm)],
% 3.02/0.98                [c_775,c_25]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_19,plain,
% 3.02/0.98      ( ~ m2_connsp_2(X0,X1,X2)
% 3.02/0.98      | r1_tarski(X2,k1_tops_1(X1,X0))
% 3.02/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.98      | ~ v2_pre_topc(X1)
% 3.02/0.98      | ~ l1_pre_topc(X1) ),
% 3.02/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_21,plain,
% 3.02/0.98      ( ~ m2_connsp_2(X0,X1,X2)
% 3.02/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.98      | ~ v2_pre_topc(X1)
% 3.02/0.98      | ~ l1_pre_topc(X1) ),
% 3.02/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_164,plain,
% 3.02/0.98      ( r1_tarski(X2,k1_tops_1(X1,X0))
% 3.02/0.98      | ~ m2_connsp_2(X0,X1,X2)
% 3.02/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.98      | ~ v2_pre_topc(X1)
% 3.02/0.98      | ~ l1_pre_topc(X1) ),
% 3.02/0.98      inference(global_propositional_subsumption,
% 3.02/0.98                [status(thm)],
% 3.02/0.98                [c_19,c_21]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_165,plain,
% 3.02/0.98      ( ~ m2_connsp_2(X0,X1,X2)
% 3.02/0.98      | r1_tarski(X2,k1_tops_1(X1,X0))
% 3.02/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.98      | ~ v2_pre_topc(X1)
% 3.02/0.98      | ~ l1_pre_topc(X1) ),
% 3.02/0.98      inference(renaming,[status(thm)],[c_164]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_512,plain,
% 3.02/0.98      ( ~ m2_connsp_2(X0,X1,X2)
% 3.02/0.98      | r1_tarski(X2,k1_tops_1(X1,X0))
% 3.02/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.98      | ~ v2_pre_topc(X1)
% 3.02/0.98      | sK1 != X1 ),
% 3.02/0.98      inference(resolution_lifted,[status(thm)],[c_165,c_26]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_513,plain,
% 3.02/0.98      ( ~ m2_connsp_2(X0,sK1,X1)
% 3.02/0.98      | r1_tarski(X1,k1_tops_1(sK1,X0))
% 3.02/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ v2_pre_topc(sK1) ),
% 3.02/0.98      inference(unflattening,[status(thm)],[c_512]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_517,plain,
% 3.02/0.98      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | r1_tarski(X1,k1_tops_1(sK1,X0))
% 3.02/0.98      | ~ m2_connsp_2(X0,sK1,X1) ),
% 3.02/0.98      inference(global_propositional_subsumption,
% 3.02/0.98                [status(thm)],
% 3.02/0.98                [c_513,c_27]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_518,plain,
% 3.02/0.98      ( ~ m2_connsp_2(X0,sK1,X1)
% 3.02/0.98      | r1_tarski(X1,k1_tops_1(sK1,X0))
% 3.02/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.02/0.98      inference(renaming,[status(thm)],[c_517]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_813,plain,
% 3.02/0.98      ( r1_tarski(X0,k1_tops_1(sK1,X1))
% 3.02/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 3.02/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != X0
% 3.02/0.98      | sK1 != sK1
% 3.02/0.98      | sK3 != X1 ),
% 3.02/0.98      inference(resolution_lifted,[status(thm)],[c_777,c_518]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_814,plain,
% 3.02/0.98      ( r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
% 3.02/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 3.02/0.98      inference(unflattening,[status(thm)],[c_813]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_896,plain,
% 3.02/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.02/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 3.02/0.98      | k1_tops_1(sK1,sK3) != X1
% 3.02/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != X0 ),
% 3.02/0.98      inference(resolution_lifted,[status(thm)],[c_230,c_814]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_897,plain,
% 3.02/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3)))
% 3.02/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 3.02/0.98      inference(unflattening,[status(thm)],[c_896]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1717,plain,
% 3.02/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top
% 3.02/0.98      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_897]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_29,plain,
% 3.02/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_31,plain,
% 3.02/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_32,plain,
% 3.02/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_58,plain,
% 3.02/0.98      ( v2_struct_0(X0) = iProver_top
% 3.02/0.98      | l1_struct_0(X0) != iProver_top
% 3.02/0.98      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_60,plain,
% 3.02/0.98      ( v2_struct_0(sK1) = iProver_top
% 3.02/0.98      | l1_struct_0(sK1) != iProver_top
% 3.02/0.98      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 3.02/0.98      inference(instantiation,[status(thm)],[c_58]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_61,plain,
% 3.02/0.98      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_63,plain,
% 3.02/0.98      ( l1_pre_topc(sK1) != iProver_top
% 3.02/0.98      | l1_struct_0(sK1) = iProver_top ),
% 3.02/0.98      inference(instantiation,[status(thm)],[c_61]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_898,plain,
% 3.02/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top
% 3.02/0.98      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_897]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_14,plain,
% 3.02/0.98      ( ~ m1_subset_1(X0,X1)
% 3.02/0.98      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 3.02/0.98      | v1_xboole_0(X1) ),
% 3.02/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1884,plain,
% 3.02/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.02/0.98      | v1_xboole_0(u1_struct_0(sK1)) ),
% 3.02/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1885,plain,
% 3.02/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.02/0.98      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.02/0.98      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_1884]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1950,plain,
% 3.02/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 3.02/0.98      inference(global_propositional_subsumption,
% 3.02/0.98                [status(thm)],
% 3.02/0.98                [c_1717,c_29,c_31,c_32,c_60,c_63,c_898,c_1885]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_3710,plain,
% 3.02/0.98      ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 3.02/0.98      inference(demodulation,[status(thm)],[c_3705,c_1950]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_9,plain,
% 3.02/0.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.02/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_228,plain,
% 3.02/0.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.02/0.98      inference(prop_impl,[status(thm)],[c_9]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_22,negated_conjecture,
% 3.02/0.98      ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 3.02/0.98      | ~ m1_connsp_2(sK3,sK1,sK2) ),
% 3.02/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_232,plain,
% 3.02/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 3.02/0.98      | ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
% 3.02/0.98      inference(prop_impl,[status(thm)],[c_22]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_233,plain,
% 3.02/0.98      ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 3.02/0.98      | ~ m1_connsp_2(sK3,sK1,sK2) ),
% 3.02/0.98      inference(renaming,[status(thm)],[c_232]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_16,plain,
% 3.02/0.98      ( m1_connsp_2(X0,X1,X2)
% 3.02/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.02/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 3.02/0.98      | ~ v2_pre_topc(X1)
% 3.02/0.98      | v2_struct_0(X1)
% 3.02/0.98      | ~ l1_pre_topc(X1) ),
% 3.02/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_473,plain,
% 3.02/0.98      ( m1_connsp_2(X0,X1,X2)
% 3.02/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.02/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 3.02/0.98      | ~ v2_pre_topc(X1)
% 3.02/0.98      | ~ l1_pre_topc(X1)
% 3.02/0.98      | sK1 != X1 ),
% 3.02/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_28]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_474,plain,
% 3.02/0.98      ( m1_connsp_2(X0,sK1,X1)
% 3.02/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.02/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 3.02/0.98      | ~ v2_pre_topc(sK1)
% 3.02/0.98      | ~ l1_pre_topc(sK1) ),
% 3.02/0.98      inference(unflattening,[status(thm)],[c_473]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_478,plain,
% 3.02/0.98      ( m1_connsp_2(X0,sK1,X1)
% 3.02/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.02/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 3.02/0.98      inference(global_propositional_subsumption,
% 3.02/0.98                [status(thm)],
% 3.02/0.98                [c_474,c_27,c_26]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_788,plain,
% 3.02/0.98      ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 3.02/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.02/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
% 3.02/0.98      | sK2 != X0
% 3.02/0.98      | sK1 != sK1
% 3.02/0.98      | sK3 != X1 ),
% 3.02/0.98      inference(resolution_lifted,[status(thm)],[c_233,c_478]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_789,plain,
% 3.02/0.98      ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 3.02/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.02/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 3.02/0.98      inference(unflattening,[status(thm)],[c_788]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_24,negated_conjecture,
% 3.02/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.02/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_791,plain,
% 3.02/0.98      ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 3.02/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 3.02/0.98      inference(global_propositional_subsumption,
% 3.02/0.98                [status(thm)],
% 3.02/0.98                [c_789,c_25,c_24]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_18,plain,
% 3.02/0.98      ( m2_connsp_2(X0,X1,X2)
% 3.02/0.98      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 3.02/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.98      | ~ v2_pre_topc(X1)
% 3.02/0.98      | ~ l1_pre_topc(X1) ),
% 3.02/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_550,plain,
% 3.02/0.98      ( m2_connsp_2(X0,X1,X2)
% 3.02/0.98      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 3.02/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.98      | ~ v2_pre_topc(X1)
% 3.02/0.98      | sK1 != X1 ),
% 3.02/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_551,plain,
% 3.02/0.98      ( m2_connsp_2(X0,sK1,X1)
% 3.02/0.98      | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 3.02/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ v2_pre_topc(sK1) ),
% 3.02/0.98      inference(unflattening,[status(thm)],[c_550]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_555,plain,
% 3.02/0.98      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 3.02/0.98      | m2_connsp_2(X0,sK1,X1) ),
% 3.02/0.98      inference(global_propositional_subsumption,
% 3.02/0.98                [status(thm)],
% 3.02/0.98                [c_551,c_27]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_556,plain,
% 3.02/0.98      ( m2_connsp_2(X0,sK1,X1)
% 3.02/0.98      | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 3.02/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.02/0.98      inference(renaming,[status(thm)],[c_555]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_826,plain,
% 3.02/0.98      ( ~ r1_tarski(X0,k1_tops_1(sK1,X1))
% 3.02/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 3.02/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != X0
% 3.02/0.98      | sK1 != sK1
% 3.02/0.98      | sK3 != X1 ),
% 3.02/0.98      inference(resolution_lifted,[status(thm)],[c_791,c_556]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_827,plain,
% 3.02/0.98      ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
% 3.02/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 3.02/0.98      inference(unflattening,[status(thm)],[c_826]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_829,plain,
% 3.02/0.98      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
% 3.02/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 3.02/0.98      inference(global_propositional_subsumption,
% 3.02/0.98                [status(thm)],
% 3.02/0.98                [c_827,c_24]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_830,plain,
% 3.02/0.98      ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
% 3.02/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 3.02/0.98      inference(renaming,[status(thm)],[c_829]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_865,plain,
% 3.02/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.02/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 3.02/0.98      | k1_tops_1(sK1,sK3) != X1
% 3.02/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != X0 ),
% 3.02/0.98      inference(resolution_lifted,[status(thm)],[c_228,c_830]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_866,plain,
% 3.02/0.98      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3)))
% 3.02/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 3.02/0.98      inference(unflattening,[status(thm)],[c_865]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1720,plain,
% 3.02/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) != iProver_top
% 3.02/0.98      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_866]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_867,plain,
% 3.02/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) != iProver_top
% 3.02/0.98      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_866]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1943,plain,
% 3.02/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) != iProver_top
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
% 3.02/0.98      inference(global_propositional_subsumption,
% 3.02/0.98                [status(thm)],
% 3.02/0.98                [c_1720,c_29,c_31,c_32,c_60,c_63,c_867,c_1885]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_3711,plain,
% 3.02/0.98      ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) != iProver_top
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
% 3.02/0.98      inference(demodulation,[status(thm)],[c_3705,c_1943]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_6,plain,
% 3.02/0.98      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
% 3.02/0.98      | ~ r2_hidden(X0,X1) ),
% 3.02/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_2302,plain,
% 3.02/0.98      ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3)))
% 3.02/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 3.02/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_2303,plain,
% 3.02/0.98      ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_2302]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_4107,plain,
% 3.02/0.98      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
% 3.02/0.98      inference(global_propositional_subsumption,
% 3.02/0.98                [status(thm)],
% 3.02/0.98                [c_3711,c_2303]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_4538,plain,
% 3.02/0.98      ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top ),
% 3.02/0.98      inference(global_propositional_subsumption,
% 3.02/0.98                [status(thm)],
% 3.02/0.98                [c_3710,c_2303,c_3711]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_10,plain,
% 3.02/0.98      ( m1_subset_1(X0,X1)
% 3.02/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.02/0.98      | ~ r2_hidden(X0,X2) ),
% 3.02/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1727,plain,
% 3.02/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 3.02/0.98      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.02/0.98      | r2_hidden(X0,X2) != iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_4545,plain,
% 3.02/0.98      ( m1_subset_1(X0,k1_tops_1(sK1,sK3)) = iProver_top
% 3.02/0.98      | r2_hidden(X0,k2_tarski(sK2,sK2)) != iProver_top ),
% 3.02/0.98      inference(superposition,[status(thm)],[c_4538,c_1727]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_4936,plain,
% 3.02/0.98      ( m1_subset_1(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 3.02/0.98      inference(superposition,[status(thm)],[c_1732,c_4545]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_7,plain,
% 3.02/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.02/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1728,plain,
% 3.02/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.02/0.98      | r2_hidden(X0,X1) = iProver_top
% 3.02/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_5782,plain,
% 3.02/0.98      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
% 3.02/0.98      | v1_xboole_0(k1_tops_1(sK1,sK3)) = iProver_top ),
% 3.02/0.98      inference(superposition,[status(thm)],[c_4936,c_1728]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_11,plain,
% 3.02/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.02/0.98      | ~ r2_hidden(X2,X0)
% 3.02/0.98      | ~ v1_xboole_0(X1) ),
% 3.02/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_295,plain,
% 3.02/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 3.02/0.98      inference(bin_hyper_res,[status(thm)],[c_11,c_230]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_878,plain,
% 3.02/0.98      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ r2_hidden(X0,X1)
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 3.02/0.98      | ~ v1_xboole_0(X2)
% 3.02/0.98      | k1_tops_1(sK1,sK3) != X2
% 3.02/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != X1 ),
% 3.02/0.98      inference(resolution_lifted,[status(thm)],[c_295,c_814]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_879,plain,
% 3.02/0.98      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK1),sK2))
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 3.02/0.98      | ~ v1_xboole_0(k1_tops_1(sK1,sK3)) ),
% 3.02/0.98      inference(unflattening,[status(thm)],[c_878]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1385,plain,
% 3.02/0.98      ( ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK1),sK2))
% 3.02/0.98      | ~ sP0_iProver_split ),
% 3.02/0.98      inference(splitting,
% 3.02/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.02/0.98                [c_879]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1719,plain,
% 3.02/0.98      ( r2_hidden(X0,k6_domain_1(u1_struct_0(sK1),sK2)) != iProver_top
% 3.02/0.98      | sP0_iProver_split != iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_1385]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_3712,plain,
% 3.02/0.98      ( r2_hidden(X0,k2_tarski(sK2,sK2)) != iProver_top
% 3.02/0.98      | sP0_iProver_split != iProver_top ),
% 3.02/0.98      inference(demodulation,[status(thm)],[c_3705,c_1719]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_3918,plain,
% 3.02/0.98      ( sP0_iProver_split != iProver_top ),
% 3.02/0.98      inference(superposition,[status(thm)],[c_1732,c_3712]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1386,plain,
% 3.02/0.98      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 3.02/0.98      | ~ v1_xboole_0(k1_tops_1(sK1,sK3))
% 3.02/0.98      | sP0_iProver_split ),
% 3.02/0.98      inference(splitting,
% 3.02/0.98                [splitting(split),new_symbols(definition,[])],
% 3.02/0.98                [c_879]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1718,plain,
% 3.02/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
% 3.02/0.98      | v1_xboole_0(k1_tops_1(sK1,sK3)) != iProver_top
% 3.02/0.98      | sP0_iProver_split = iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_1386]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1407,plain,
% 3.02/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.02/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
% 3.02/0.98      | v1_xboole_0(k1_tops_1(sK1,sK3)) != iProver_top
% 3.02/0.98      | sP0_iProver_split = iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_1386]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_2067,plain,
% 3.02/0.98      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
% 3.02/0.98      | v1_xboole_0(k1_tops_1(sK1,sK3)) != iProver_top
% 3.02/0.98      | sP0_iProver_split = iProver_top ),
% 3.02/0.98      inference(global_propositional_subsumption,
% 3.02/0.98                [status(thm)],
% 3.02/0.98                [c_1718,c_29,c_31,c_32,c_60,c_63,c_1407,c_1885]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1729,plain,
% 3.02/0.98      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 3.02/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1726,plain,
% 3.02/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.02/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.02/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_2382,plain,
% 3.02/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.02/0.98      | r2_hidden(X2,k2_tarski(X0,X0)) != iProver_top
% 3.02/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.02/0.98      inference(superposition,[status(thm)],[c_1729,c_1726]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_2727,plain,
% 3.02/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.02/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.02/0.98      inference(superposition,[status(thm)],[c_1732,c_2382]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_2826,plain,
% 3.02/0.98      ( v1_xboole_0(k1_tops_1(sK1,sK3)) != iProver_top
% 3.02/0.98      | sP0_iProver_split = iProver_top ),
% 3.02/0.98      inference(superposition,[status(thm)],[c_2067,c_2727]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(contradiction,plain,
% 3.02/0.98      ( $false ),
% 3.02/0.98      inference(minisat,[status(thm)],[c_5782,c_4107,c_3918,c_2826]) ).
% 3.02/0.98  
% 3.02/0.98  
% 3.02/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.02/0.98  
% 3.02/0.98  ------                               Statistics
% 3.02/0.98  
% 3.02/0.98  ------ General
% 3.02/0.98  
% 3.02/0.98  abstr_ref_over_cycles:                  0
% 3.02/0.98  abstr_ref_under_cycles:                 0
% 3.02/0.98  gc_basic_clause_elim:                   0
% 3.02/0.98  forced_gc_time:                         0
% 3.02/0.98  parsing_time:                           0.009
% 3.02/0.98  unif_index_cands_time:                  0.
% 3.02/0.98  unif_index_add_time:                    0.
% 3.02/0.98  orderings_time:                         0.
% 3.02/0.98  out_proof_time:                         0.012
% 3.02/0.98  total_time:                             0.183
% 3.02/0.98  num_of_symbols:                         51
% 3.02/0.98  num_of_terms:                           5920
% 3.02/0.98  
% 3.02/0.98  ------ Preprocessing
% 3.02/0.98  
% 3.02/0.98  num_of_splits:                          1
% 3.02/0.98  num_of_split_atoms:                     1
% 3.02/0.98  num_of_reused_defs:                     0
% 3.02/0.98  num_eq_ax_congr_red:                    19
% 3.02/0.98  num_of_sem_filtered_clauses:            1
% 3.02/0.98  num_of_subtypes:                        0
% 3.02/0.98  monotx_restored_types:                  0
% 3.02/0.98  sat_num_of_epr_types:                   0
% 3.02/0.98  sat_num_of_non_cyclic_types:            0
% 3.02/0.98  sat_guarded_non_collapsed_types:        0
% 3.02/0.98  num_pure_diseq_elim:                    0
% 3.02/0.98  simp_replaced_by:                       0
% 3.02/0.98  res_preprocessed:                       104
% 3.02/0.98  prep_upred:                             0
% 3.02/0.98  prep_unflattend:                        46
% 3.02/0.98  smt_new_axioms:                         0
% 3.02/0.98  pred_elim_cands:                        3
% 3.02/0.98  pred_elim:                              7
% 3.02/0.98  pred_elim_cl:                           11
% 3.02/0.98  pred_elim_cycles:                       11
% 3.02/0.98  merged_defs:                            4
% 3.02/0.98  merged_defs_ncl:                        0
% 3.02/0.98  bin_hyper_res:                          5
% 3.02/0.98  prep_cycles:                            4
% 3.02/0.98  pred_elim_time:                         0.016
% 3.02/0.98  splitting_time:                         0.
% 3.02/0.98  sem_filter_time:                        0.
% 3.02/0.98  monotx_time:                            0.001
% 3.02/0.98  subtype_inf_time:                       0.
% 3.02/0.98  
% 3.02/0.98  ------ Problem properties
% 3.02/0.98  
% 3.02/0.98  clauses:                                19
% 3.02/0.98  conjectures:                            2
% 3.02/0.98  epr:                                    1
% 3.02/0.98  horn:                                   12
% 3.02/0.98  ground:                                 6
% 3.02/0.98  unary:                                  5
% 3.02/0.98  binary:                                 2
% 3.02/0.98  lits:                                   47
% 3.02/0.98  lits_eq:                                10
% 3.02/0.98  fd_pure:                                0
% 3.02/0.98  fd_pseudo:                              0
% 3.02/0.98  fd_cond:                                0
% 3.02/0.98  fd_pseudo_cond:                         3
% 3.02/0.98  ac_symbols:                             0
% 3.02/0.98  
% 3.02/0.98  ------ Propositional Solver
% 3.02/0.98  
% 3.02/0.98  prop_solver_calls:                      28
% 3.02/0.98  prop_fast_solver_calls:                 875
% 3.02/0.98  smt_solver_calls:                       0
% 3.02/0.98  smt_fast_solver_calls:                  0
% 3.02/0.98  prop_num_of_clauses:                    2059
% 3.02/0.98  prop_preprocess_simplified:             6652
% 3.02/0.98  prop_fo_subsumed:                       29
% 3.02/0.98  prop_solver_time:                       0.
% 3.02/0.98  smt_solver_time:                        0.
% 3.02/0.98  smt_fast_solver_time:                   0.
% 3.02/0.98  prop_fast_solver_time:                  0.
% 3.02/0.98  prop_unsat_core_time:                   0.
% 3.02/0.98  
% 3.02/0.98  ------ QBF
% 3.02/0.98  
% 3.02/0.98  qbf_q_res:                              0
% 3.02/0.98  qbf_num_tautologies:                    0
% 3.02/0.98  qbf_prep_cycles:                        0
% 3.02/0.98  
% 3.02/0.98  ------ BMC1
% 3.02/0.98  
% 3.02/0.98  bmc1_current_bound:                     -1
% 3.02/0.98  bmc1_last_solved_bound:                 -1
% 3.02/0.98  bmc1_unsat_core_size:                   -1
% 3.02/0.98  bmc1_unsat_core_parents_size:           -1
% 3.02/0.98  bmc1_merge_next_fun:                    0
% 3.02/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.02/0.98  
% 3.02/0.98  ------ Instantiation
% 3.02/0.98  
% 3.02/0.98  inst_num_of_clauses:                    556
% 3.02/0.98  inst_num_in_passive:                    317
% 3.02/0.98  inst_num_in_active:                     221
% 3.02/0.98  inst_num_in_unprocessed:                18
% 3.02/0.98  inst_num_of_loops:                      240
% 3.02/0.98  inst_num_of_learning_restarts:          0
% 3.02/0.98  inst_num_moves_active_passive:          17
% 3.02/0.98  inst_lit_activity:                      0
% 3.02/0.98  inst_lit_activity_moves:                0
% 3.02/0.98  inst_num_tautologies:                   0
% 3.02/0.98  inst_num_prop_implied:                  0
% 3.02/0.98  inst_num_existing_simplified:           0
% 3.02/0.98  inst_num_eq_res_simplified:             0
% 3.02/0.98  inst_num_child_elim:                    0
% 3.02/0.98  inst_num_of_dismatching_blockings:      181
% 3.02/0.98  inst_num_of_non_proper_insts:           473
% 3.02/0.98  inst_num_of_duplicates:                 0
% 3.02/0.98  inst_inst_num_from_inst_to_res:         0
% 3.02/0.98  inst_dismatching_checking_time:         0.
% 3.02/0.98  
% 3.02/0.98  ------ Resolution
% 3.02/0.98  
% 3.02/0.98  res_num_of_clauses:                     0
% 3.02/0.98  res_num_in_passive:                     0
% 3.02/0.98  res_num_in_active:                      0
% 3.02/0.98  res_num_of_loops:                       108
% 3.02/0.98  res_forward_subset_subsumed:            125
% 3.02/0.98  res_backward_subset_subsumed:           0
% 3.02/0.98  res_forward_subsumed:                   0
% 3.02/0.98  res_backward_subsumed:                  0
% 3.02/0.98  res_forward_subsumption_resolution:     0
% 3.02/0.98  res_backward_subsumption_resolution:    0
% 3.02/0.98  res_clause_to_clause_subsumption:       246
% 3.02/0.98  res_orphan_elimination:                 0
% 3.02/0.98  res_tautology_del:                      46
% 3.02/0.98  res_num_eq_res_simplified:              0
% 3.02/0.98  res_num_sel_changes:                    0
% 3.02/0.98  res_moves_from_active_to_pass:          0
% 3.02/0.98  
% 3.02/0.98  ------ Superposition
% 3.02/0.98  
% 3.02/0.98  sup_time_total:                         0.
% 3.02/0.98  sup_time_generating:                    0.
% 3.02/0.98  sup_time_sim_full:                      0.
% 3.02/0.98  sup_time_sim_immed:                     0.
% 3.02/0.98  
% 3.02/0.98  sup_num_of_clauses:                     65
% 3.02/0.98  sup_num_in_active:                      40
% 3.02/0.98  sup_num_in_passive:                     25
% 3.02/0.98  sup_num_of_loops:                       46
% 3.02/0.98  sup_fw_superposition:                   49
% 3.02/0.98  sup_bw_superposition:                   28
% 3.02/0.98  sup_immediate_simplified:               11
% 3.02/0.98  sup_given_eliminated:                   1
% 3.02/0.98  comparisons_done:                       0
% 3.02/0.98  comparisons_avoided:                    3
% 3.02/0.98  
% 3.02/0.98  ------ Simplifications
% 3.02/0.98  
% 3.02/0.98  
% 3.02/0.98  sim_fw_subset_subsumed:                 9
% 3.02/0.98  sim_bw_subset_subsumed:                 3
% 3.02/0.98  sim_fw_subsumed:                        2
% 3.02/0.98  sim_bw_subsumed:                        1
% 3.02/0.98  sim_fw_subsumption_res:                 0
% 3.02/0.98  sim_bw_subsumption_res:                 0
% 3.02/0.98  sim_tautology_del:                      3
% 3.02/0.98  sim_eq_tautology_del:                   1
% 3.02/0.98  sim_eq_res_simp:                        0
% 3.02/0.98  sim_fw_demodulated:                     0
% 3.02/0.98  sim_bw_demodulated:                     5
% 3.02/0.98  sim_light_normalised:                   0
% 3.02/0.98  sim_joinable_taut:                      0
% 3.02/0.98  sim_joinable_simp:                      0
% 3.02/0.98  sim_ac_normalised:                      0
% 3.02/0.98  sim_smt_subsumption:                    0
% 3.02/0.98  
%------------------------------------------------------------------------------
