%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:49 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  232 (1410 expanded)
%              Number of clauses        :  136 ( 383 expanded)
%              Number of leaves         :   25 ( 308 expanded)
%              Depth                    :   21
%              Number of atoms          :  867 (9431 expanded)
%              Number of equality atoms :  241 ( 570 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f55,f56])).

fof(f70,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f65,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK3)
          | ~ v2_tex_2(sK3,X0) )
        & ( v1_zfmisc_1(sK3)
          | v2_tex_2(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK2) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ( ~ v1_zfmisc_1(sK3)
      | ~ v2_tex_2(sK3,sK2) )
    & ( v1_zfmisc_1(sK3)
      | v2_tex_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & ~ v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f65,f67,f66])).

fof(f105,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f68])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f95,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f107,plain,
    ( v1_zfmisc_1(sK3)
    | v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f106,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f68])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK1(X0,X1)) = X1
        & m1_pre_topc(sK1(X0,X1),X0)
        & v1_tdlat_3(sK1(X0,X1))
        & ~ v2_struct_0(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK1(X0,X1)) = X1
            & m1_pre_topc(sK1(X0,X1),X0)
            & v1_tdlat_3(sK1(X0,X1))
            & ~ v2_struct_0(sK1(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f62])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK1(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f101,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f102,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f104,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f85,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f103,plain,(
    v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f108,plain,
    ( ~ v1_zfmisc_1(sK3)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f58])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f110,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f92,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f90,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f84,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f86,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK1(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f99,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK1(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_243,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_1])).

cnf(c_244,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_243])).

cnf(c_551,plain,
    ( m1_subset_1(X0,X1)
    | v1_xboole_0(X2)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_244])).

cnf(c_552,plain,
    ( m1_subset_1(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_4020,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4039,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6852,plain,
    ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4020,c_4039])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_4028,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_7295,plain,
    ( k6_domain_1(sK3,sK0(sK3)) = k1_tarski(sK0(sK3)) ),
    inference(superposition,[status(thm)],[c_6852,c_4028])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4040,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7507,plain,
    ( m1_subset_1(k1_tarski(sK0(sK3)),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK0(sK3),sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7295,c_4040])).

cnf(c_44,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4339,plain,
    ( m1_subset_1(sK0(sK3),sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_552])).

cnf(c_4340,plain,
    ( m1_subset_1(sK0(sK3),sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4339])).

cnf(c_7740,plain,
    ( m1_subset_1(k1_tarski(sK0(sK3)),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7507,c_44,c_4340])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_4042,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7746,plain,
    ( r1_tarski(k1_tarski(sK0(sK3)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7740,c_4042])).

cnf(c_26,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_218,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_12,c_11])).

cnf(c_219,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_218])).

cnf(c_4023,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_8957,plain,
    ( k1_tarski(sK0(sK3)) = sK3
    | v1_zfmisc_1(sK3) != iProver_top
    | v1_xboole_0(k1_tarski(sK0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7746,c_4023])).

cnf(c_33,negated_conjecture,
    ( v2_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_46,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_4029,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_28,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK1(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_4035,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_pre_topc(sK1(X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7072,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | m1_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4029,c_4035])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_40,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_41,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_43,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_7582,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | m1_pre_topc(sK1(sK2,sK3),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7072,c_40,c_41,c_43,c_44])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4041,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7589,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | l1_pre_topc(sK1(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7582,c_4041])).

cnf(c_37,negated_conjecture,
    ( v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_42,plain,
    ( v2_tdlat_3(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_32,negated_conjecture,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_47,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v1_zfmisc_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_4559,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_23,plain,
    ( v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_21,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_224,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_21])).

cnf(c_225,plain,
    ( v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_224])).

cnf(c_15,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_17,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_505,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_15,c_17])).

cnf(c_523,plain,
    ( v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_225,c_505])).

cnf(c_4641,plain,
    ( v2_struct_0(sK1(X0,sK3))
    | ~ v2_tdlat_3(sK1(X0,sK3))
    | ~ v1_tdlat_3(sK1(X0,sK3))
    | v1_zfmisc_1(u1_struct_0(sK1(X0,sK3)))
    | ~ l1_pre_topc(sK1(X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_4642,plain,
    ( v2_struct_0(sK1(X0,sK3)) = iProver_top
    | v2_tdlat_3(sK1(X0,sK3)) != iProver_top
    | v1_tdlat_3(sK1(X0,sK3)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1(X0,sK3))) = iProver_top
    | l1_pre_topc(sK1(X0,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4641])).

cnf(c_4644,plain,
    ( v2_struct_0(sK1(sK2,sK3)) = iProver_top
    | v2_tdlat_3(sK1(sK2,sK3)) != iProver_top
    | v1_tdlat_3(sK1(sK2,sK3)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3))) = iProver_top
    | l1_pre_topc(sK1(sK2,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4642])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4526,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4763,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_4526])).

cnf(c_3209,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4525,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_3209])).

cnf(c_4776,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4525])).

cnf(c_5206,plain,
    ( u1_struct_0(sK1(X0,sK3)) != sK3
    | sK3 = u1_struct_0(sK1(X0,sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4776])).

cnf(c_5207,plain,
    ( u1_struct_0(sK1(sK2,sK3)) != sK3
    | sK3 = u1_struct_0(sK1(sK2,sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_5206])).

cnf(c_3216,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_zfmisc_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5053,plain,
    ( v1_zfmisc_1(X0)
    | ~ v1_zfmisc_1(u1_struct_0(sK1(X1,sK3)))
    | X0 != u1_struct_0(sK1(X1,sK3)) ),
    inference(instantiation,[status(thm)],[c_3216])).

cnf(c_5696,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK1(X0,sK3)))
    | v1_zfmisc_1(sK3)
    | sK3 != u1_struct_0(sK1(X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_5053])).

cnf(c_5697,plain,
    ( sK3 != u1_struct_0(sK1(X0,sK3))
    | v1_zfmisc_1(u1_struct_0(sK1(X0,sK3))) != iProver_top
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5696])).

cnf(c_5699,plain,
    ( sK3 != u1_struct_0(sK1(sK2,sK3))
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3))) != iProver_top
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5697])).

cnf(c_29,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_tdlat_3(sK1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_4034,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_tdlat_3(sK1(X1,X0)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6070,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_tdlat_3(sK1(sK2,sK3)) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4029,c_4034])).

cnf(c_6438,plain,
    ( v1_tdlat_3(sK1(sK2,sK3)) = iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6070,c_40,c_41,c_43,c_44])).

cnf(c_6439,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v1_tdlat_3(sK1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6438])).

cnf(c_27,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_4036,plain,
    ( u1_struct_0(sK1(X0,X1)) = X1
    | v2_tex_2(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6255,plain,
    ( u1_struct_0(sK1(sK2,sK3)) = sK3
    | v2_tex_2(sK3,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4029,c_4036])).

cnf(c_6445,plain,
    ( u1_struct_0(sK1(sK2,sK3)) = sK3
    | v2_tex_2(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6255,c_40,c_41,c_43,c_44])).

cnf(c_30,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_4033,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK1(X1,X0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6973,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v2_struct_0(sK1(sK2,sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4029,c_4033])).

cnf(c_7510,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v2_struct_0(sK1(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6973,c_40,c_41,c_43,c_44])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1226,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X2)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_1227,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_1226])).

cnf(c_4018,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_tdlat_3(X1) != iProver_top
    | v2_tdlat_3(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1227])).

cnf(c_7588,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_tdlat_3(sK1(sK2,sK3)) = iProver_top
    | v2_tdlat_3(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7582,c_4018])).

cnf(c_7672,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7589,c_40,c_42,c_43,c_47,c_4559,c_4644,c_4763,c_5207,c_5699,c_6439,c_6445,c_7510,c_7588])).

cnf(c_9620,plain,
    ( k1_tarski(sK0(sK3)) = sK3
    | v1_xboole_0(k1_tarski(sK0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8957,c_40,c_42,c_43,c_46,c_47,c_4559,c_4644,c_4763,c_5207,c_5699,c_6439,c_6445,c_7510,c_7588,c_7589])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4046,plain,
    ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9626,plain,
    ( k1_tarski(sK0(sK3)) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9620,c_4046])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_14,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | v1_xboole_0(X1)
    | X2 != X0
    | X4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_581,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_580])).

cnf(c_4019,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_581])).

cnf(c_5812,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4029,c_4019])).

cnf(c_6326,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5812,c_44])).

cnf(c_6327,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_6326])).

cnf(c_6335,plain,
    ( k6_domain_1(u1_struct_0(sK2),X0) = k1_tarski(X0)
    | m1_subset_1(X0,sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6327,c_4039])).

cnf(c_4602,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4029,c_4042])).

cnf(c_305,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_306,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_305])).

cnf(c_372,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_306])).

cnf(c_4022,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_4922,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4602,c_4022])).

cnf(c_6491,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | k6_domain_1(u1_struct_0(sK2),X0) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6335,c_44,c_4922])).

cnf(c_6492,plain,
    ( k6_domain_1(u1_struct_0(sK2),X0) = k1_tarski(X0)
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_6491])).

cnf(c_6854,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3))
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4020,c_6492])).

cnf(c_4430,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_581])).

cnf(c_4581,plain,
    ( m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4430])).

cnf(c_4867,plain,
    ( m1_subset_1(sK0(sK3),u1_struct_0(X0))
    | ~ m1_subset_1(sK0(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4581])).

cnf(c_4869,plain,
    ( m1_subset_1(sK0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4867])).

cnf(c_4927,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4922])).

cnf(c_4838,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X1))
    | k6_domain_1(u1_struct_0(X1),X0) = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_6160,plain,
    ( ~ m1_subset_1(sK0(sK3),u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(X0))
    | k6_domain_1(u1_struct_0(X0),sK0(sK3)) = k1_tarski(sK0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4838])).

cnf(c_6162,plain,
    ( ~ m1_subset_1(sK0(sK3),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3)) ),
    inference(instantiation,[status(thm)],[c_6160])).

cnf(c_8157,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6854,c_35,c_34,c_4339,c_4869,c_4927,c_6162])).

cnf(c_9629,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_9626,c_8157])).

cnf(c_31,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_4032,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_10791,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top
    | m1_subset_1(sK0(sK3),u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9629,c_4032])).

cnf(c_4868,plain,
    ( m1_subset_1(sK0(sK3),u1_struct_0(X0)) = iProver_top
    | m1_subset_1(sK0(sK3),sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4867])).

cnf(c_4870,plain,
    ( m1_subset_1(sK0(sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK0(sK3),sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4868])).

cnf(c_45,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10791,c_7672,c_4870,c_4340,c_45,c_44,c_43,c_41,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:00:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 3.65/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/0.99  
% 3.65/0.99  ------  iProver source info
% 3.65/0.99  
% 3.65/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.65/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/0.99  git: non_committed_changes: false
% 3.65/0.99  git: last_make_outside_of_git: false
% 3.65/0.99  
% 3.65/0.99  ------ 
% 3.65/0.99  
% 3.65/0.99  ------ Input Options
% 3.65/0.99  
% 3.65/0.99  --out_options                           all
% 3.65/0.99  --tptp_safe_out                         true
% 3.65/0.99  --problem_path                          ""
% 3.65/0.99  --include_path                          ""
% 3.65/0.99  --clausifier                            res/vclausify_rel
% 3.65/0.99  --clausifier_options                    --mode clausify
% 3.65/0.99  --stdin                                 false
% 3.65/0.99  --stats_out                             all
% 3.65/0.99  
% 3.65/0.99  ------ General Options
% 3.65/0.99  
% 3.65/0.99  --fof                                   false
% 3.65/0.99  --time_out_real                         305.
% 3.65/0.99  --time_out_virtual                      -1.
% 3.65/0.99  --symbol_type_check                     false
% 3.65/0.99  --clausify_out                          false
% 3.65/0.99  --sig_cnt_out                           false
% 3.65/0.99  --trig_cnt_out                          false
% 3.65/0.99  --trig_cnt_out_tolerance                1.
% 3.65/0.99  --trig_cnt_out_sk_spl                   false
% 3.65/0.99  --abstr_cl_out                          false
% 3.65/0.99  
% 3.65/0.99  ------ Global Options
% 3.65/0.99  
% 3.65/0.99  --schedule                              default
% 3.65/0.99  --add_important_lit                     false
% 3.65/0.99  --prop_solver_per_cl                    1000
% 3.65/0.99  --min_unsat_core                        false
% 3.65/0.99  --soft_assumptions                      false
% 3.65/0.99  --soft_lemma_size                       3
% 3.65/0.99  --prop_impl_unit_size                   0
% 3.65/0.99  --prop_impl_unit                        []
% 3.65/0.99  --share_sel_clauses                     true
% 3.65/0.99  --reset_solvers                         false
% 3.65/0.99  --bc_imp_inh                            [conj_cone]
% 3.65/0.99  --conj_cone_tolerance                   3.
% 3.65/0.99  --extra_neg_conj                        none
% 3.65/0.99  --large_theory_mode                     true
% 3.65/0.99  --prolific_symb_bound                   200
% 3.65/0.99  --lt_threshold                          2000
% 3.65/0.99  --clause_weak_htbl                      true
% 3.65/0.99  --gc_record_bc_elim                     false
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing Options
% 3.65/0.99  
% 3.65/0.99  --preprocessing_flag                    true
% 3.65/0.99  --time_out_prep_mult                    0.1
% 3.65/0.99  --splitting_mode                        input
% 3.65/0.99  --splitting_grd                         true
% 3.65/0.99  --splitting_cvd                         false
% 3.65/0.99  --splitting_cvd_svl                     false
% 3.65/0.99  --splitting_nvd                         32
% 3.65/0.99  --sub_typing                            true
% 3.65/0.99  --prep_gs_sim                           true
% 3.65/0.99  --prep_unflatten                        true
% 3.65/0.99  --prep_res_sim                          true
% 3.65/0.99  --prep_upred                            true
% 3.65/0.99  --prep_sem_filter                       exhaustive
% 3.65/0.99  --prep_sem_filter_out                   false
% 3.65/0.99  --pred_elim                             true
% 3.65/0.99  --res_sim_input                         true
% 3.65/0.99  --eq_ax_congr_red                       true
% 3.65/0.99  --pure_diseq_elim                       true
% 3.65/0.99  --brand_transform                       false
% 3.65/0.99  --non_eq_to_eq                          false
% 3.65/0.99  --prep_def_merge                        true
% 3.65/0.99  --prep_def_merge_prop_impl              false
% 3.65/0.99  --prep_def_merge_mbd                    true
% 3.65/0.99  --prep_def_merge_tr_red                 false
% 3.65/0.99  --prep_def_merge_tr_cl                  false
% 3.65/0.99  --smt_preprocessing                     true
% 3.65/0.99  --smt_ac_axioms                         fast
% 3.65/0.99  --preprocessed_out                      false
% 3.65/0.99  --preprocessed_stats                    false
% 3.65/0.99  
% 3.65/0.99  ------ Abstraction refinement Options
% 3.65/0.99  
% 3.65/0.99  --abstr_ref                             []
% 3.65/0.99  --abstr_ref_prep                        false
% 3.65/0.99  --abstr_ref_until_sat                   false
% 3.65/0.99  --abstr_ref_sig_restrict                funpre
% 3.65/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/0.99  --abstr_ref_under                       []
% 3.65/0.99  
% 3.65/0.99  ------ SAT Options
% 3.65/0.99  
% 3.65/0.99  --sat_mode                              false
% 3.65/0.99  --sat_fm_restart_options                ""
% 3.65/0.99  --sat_gr_def                            false
% 3.65/0.99  --sat_epr_types                         true
% 3.65/0.99  --sat_non_cyclic_types                  false
% 3.65/0.99  --sat_finite_models                     false
% 3.65/0.99  --sat_fm_lemmas                         false
% 3.65/0.99  --sat_fm_prep                           false
% 3.65/0.99  --sat_fm_uc_incr                        true
% 3.65/0.99  --sat_out_model                         small
% 3.65/0.99  --sat_out_clauses                       false
% 3.65/0.99  
% 3.65/0.99  ------ QBF Options
% 3.65/0.99  
% 3.65/0.99  --qbf_mode                              false
% 3.65/0.99  --qbf_elim_univ                         false
% 3.65/0.99  --qbf_dom_inst                          none
% 3.65/0.99  --qbf_dom_pre_inst                      false
% 3.65/0.99  --qbf_sk_in                             false
% 3.65/0.99  --qbf_pred_elim                         true
% 3.65/0.99  --qbf_split                             512
% 3.65/0.99  
% 3.65/0.99  ------ BMC1 Options
% 3.65/0.99  
% 3.65/0.99  --bmc1_incremental                      false
% 3.65/0.99  --bmc1_axioms                           reachable_all
% 3.65/0.99  --bmc1_min_bound                        0
% 3.65/0.99  --bmc1_max_bound                        -1
% 3.65/0.99  --bmc1_max_bound_default                -1
% 3.65/0.99  --bmc1_symbol_reachability              true
% 3.65/0.99  --bmc1_property_lemmas                  false
% 3.65/0.99  --bmc1_k_induction                      false
% 3.65/0.99  --bmc1_non_equiv_states                 false
% 3.65/0.99  --bmc1_deadlock                         false
% 3.65/0.99  --bmc1_ucm                              false
% 3.65/0.99  --bmc1_add_unsat_core                   none
% 3.65/0.99  --bmc1_unsat_core_children              false
% 3.65/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/0.99  --bmc1_out_stat                         full
% 3.65/0.99  --bmc1_ground_init                      false
% 3.65/0.99  --bmc1_pre_inst_next_state              false
% 3.65/0.99  --bmc1_pre_inst_state                   false
% 3.65/0.99  --bmc1_pre_inst_reach_state             false
% 3.65/0.99  --bmc1_out_unsat_core                   false
% 3.65/0.99  --bmc1_aig_witness_out                  false
% 3.65/0.99  --bmc1_verbose                          false
% 3.65/0.99  --bmc1_dump_clauses_tptp                false
% 3.65/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.65/0.99  --bmc1_dump_file                        -
% 3.65/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.65/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.65/0.99  --bmc1_ucm_extend_mode                  1
% 3.65/0.99  --bmc1_ucm_init_mode                    2
% 3.65/0.99  --bmc1_ucm_cone_mode                    none
% 3.65/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.65/0.99  --bmc1_ucm_relax_model                  4
% 3.65/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.65/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/0.99  --bmc1_ucm_layered_model                none
% 3.65/0.99  --bmc1_ucm_max_lemma_size               10
% 3.65/0.99  
% 3.65/0.99  ------ AIG Options
% 3.65/0.99  
% 3.65/0.99  --aig_mode                              false
% 3.65/0.99  
% 3.65/0.99  ------ Instantiation Options
% 3.65/0.99  
% 3.65/0.99  --instantiation_flag                    true
% 3.65/0.99  --inst_sos_flag                         false
% 3.65/0.99  --inst_sos_phase                        true
% 3.65/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/0.99  --inst_lit_sel_side                     num_symb
% 3.65/0.99  --inst_solver_per_active                1400
% 3.65/0.99  --inst_solver_calls_frac                1.
% 3.65/0.99  --inst_passive_queue_type               priority_queues
% 3.65/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/0.99  --inst_passive_queues_freq              [25;2]
% 3.65/0.99  --inst_dismatching                      true
% 3.65/0.99  --inst_eager_unprocessed_to_passive     true
% 3.65/0.99  --inst_prop_sim_given                   true
% 3.65/0.99  --inst_prop_sim_new                     false
% 3.65/0.99  --inst_subs_new                         false
% 3.65/0.99  --inst_eq_res_simp                      false
% 3.65/0.99  --inst_subs_given                       false
% 3.65/0.99  --inst_orphan_elimination               true
% 3.65/0.99  --inst_learning_loop_flag               true
% 3.65/0.99  --inst_learning_start                   3000
% 3.65/0.99  --inst_learning_factor                  2
% 3.65/0.99  --inst_start_prop_sim_after_learn       3
% 3.65/0.99  --inst_sel_renew                        solver
% 3.65/0.99  --inst_lit_activity_flag                true
% 3.65/0.99  --inst_restr_to_given                   false
% 3.65/0.99  --inst_activity_threshold               500
% 3.65/0.99  --inst_out_proof                        true
% 3.65/0.99  
% 3.65/0.99  ------ Resolution Options
% 3.65/0.99  
% 3.65/0.99  --resolution_flag                       true
% 3.65/0.99  --res_lit_sel                           adaptive
% 3.65/0.99  --res_lit_sel_side                      none
% 3.65/0.99  --res_ordering                          kbo
% 3.65/0.99  --res_to_prop_solver                    active
% 3.65/0.99  --res_prop_simpl_new                    false
% 3.65/0.99  --res_prop_simpl_given                  true
% 3.65/0.99  --res_passive_queue_type                priority_queues
% 3.65/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/0.99  --res_passive_queues_freq               [15;5]
% 3.65/0.99  --res_forward_subs                      full
% 3.65/0.99  --res_backward_subs                     full
% 3.65/0.99  --res_forward_subs_resolution           true
% 3.65/0.99  --res_backward_subs_resolution          true
% 3.65/0.99  --res_orphan_elimination                true
% 3.65/0.99  --res_time_limit                        2.
% 3.65/0.99  --res_out_proof                         true
% 3.65/0.99  
% 3.65/0.99  ------ Superposition Options
% 3.65/0.99  
% 3.65/0.99  --superposition_flag                    true
% 3.65/0.99  --sup_passive_queue_type                priority_queues
% 3.65/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.65/0.99  --demod_completeness_check              fast
% 3.65/0.99  --demod_use_ground                      true
% 3.65/0.99  --sup_to_prop_solver                    passive
% 3.65/0.99  --sup_prop_simpl_new                    true
% 3.65/0.99  --sup_prop_simpl_given                  true
% 3.65/0.99  --sup_fun_splitting                     false
% 3.65/0.99  --sup_smt_interval                      50000
% 3.65/0.99  
% 3.65/0.99  ------ Superposition Simplification Setup
% 3.65/0.99  
% 3.65/0.99  --sup_indices_passive                   []
% 3.65/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.99  --sup_full_bw                           [BwDemod]
% 3.65/0.99  --sup_immed_triv                        [TrivRules]
% 3.65/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.99  --sup_immed_bw_main                     []
% 3.65/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.99  
% 3.65/0.99  ------ Combination Options
% 3.65/0.99  
% 3.65/0.99  --comb_res_mult                         3
% 3.65/0.99  --comb_sup_mult                         2
% 3.65/0.99  --comb_inst_mult                        10
% 3.65/0.99  
% 3.65/0.99  ------ Debug Options
% 3.65/0.99  
% 3.65/0.99  --dbg_backtrace                         false
% 3.65/0.99  --dbg_dump_prop_clauses                 false
% 3.65/0.99  --dbg_dump_prop_clauses_file            -
% 3.65/0.99  --dbg_out_stat                          false
% 3.65/0.99  ------ Parsing...
% 3.65/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/0.99  ------ Proving...
% 3.65/0.99  ------ Problem Properties 
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  clauses                                 33
% 3.65/0.99  conjectures                             8
% 3.65/0.99  EPR                                     18
% 3.65/0.99  Horn                                    19
% 3.65/0.99  unary                                   8
% 3.65/0.99  binary                                  5
% 3.65/0.99  lits                                    102
% 3.65/0.99  lits eq                                 4
% 3.65/0.99  fd_pure                                 0
% 3.65/0.99  fd_pseudo                               0
% 3.65/0.99  fd_cond                                 0
% 3.65/0.99  fd_pseudo_cond                          2
% 3.65/0.99  AC symbols                              0
% 3.65/0.99  
% 3.65/0.99  ------ Schedule dynamic 5 is on 
% 3.65/0.99  
% 3.65/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  ------ 
% 3.65/0.99  Current options:
% 3.65/0.99  ------ 
% 3.65/0.99  
% 3.65/0.99  ------ Input Options
% 3.65/0.99  
% 3.65/0.99  --out_options                           all
% 3.65/0.99  --tptp_safe_out                         true
% 3.65/0.99  --problem_path                          ""
% 3.65/0.99  --include_path                          ""
% 3.65/0.99  --clausifier                            res/vclausify_rel
% 3.65/0.99  --clausifier_options                    --mode clausify
% 3.65/0.99  --stdin                                 false
% 3.65/0.99  --stats_out                             all
% 3.65/0.99  
% 3.65/0.99  ------ General Options
% 3.65/0.99  
% 3.65/0.99  --fof                                   false
% 3.65/0.99  --time_out_real                         305.
% 3.65/0.99  --time_out_virtual                      -1.
% 3.65/0.99  --symbol_type_check                     false
% 3.65/0.99  --clausify_out                          false
% 3.65/0.99  --sig_cnt_out                           false
% 3.65/0.99  --trig_cnt_out                          false
% 3.65/0.99  --trig_cnt_out_tolerance                1.
% 3.65/0.99  --trig_cnt_out_sk_spl                   false
% 3.65/0.99  --abstr_cl_out                          false
% 3.65/0.99  
% 3.65/0.99  ------ Global Options
% 3.65/0.99  
% 3.65/0.99  --schedule                              default
% 3.65/0.99  --add_important_lit                     false
% 3.65/0.99  --prop_solver_per_cl                    1000
% 3.65/0.99  --min_unsat_core                        false
% 3.65/0.99  --soft_assumptions                      false
% 3.65/0.99  --soft_lemma_size                       3
% 3.65/0.99  --prop_impl_unit_size                   0
% 3.65/0.99  --prop_impl_unit                        []
% 3.65/0.99  --share_sel_clauses                     true
% 3.65/0.99  --reset_solvers                         false
% 3.65/0.99  --bc_imp_inh                            [conj_cone]
% 3.65/0.99  --conj_cone_tolerance                   3.
% 3.65/0.99  --extra_neg_conj                        none
% 3.65/0.99  --large_theory_mode                     true
% 3.65/0.99  --prolific_symb_bound                   200
% 3.65/0.99  --lt_threshold                          2000
% 3.65/0.99  --clause_weak_htbl                      true
% 3.65/0.99  --gc_record_bc_elim                     false
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing Options
% 3.65/0.99  
% 3.65/0.99  --preprocessing_flag                    true
% 3.65/0.99  --time_out_prep_mult                    0.1
% 3.65/0.99  --splitting_mode                        input
% 3.65/0.99  --splitting_grd                         true
% 3.65/0.99  --splitting_cvd                         false
% 3.65/0.99  --splitting_cvd_svl                     false
% 3.65/0.99  --splitting_nvd                         32
% 3.65/0.99  --sub_typing                            true
% 3.65/0.99  --prep_gs_sim                           true
% 3.65/0.99  --prep_unflatten                        true
% 3.65/0.99  --prep_res_sim                          true
% 3.65/0.99  --prep_upred                            true
% 3.65/0.99  --prep_sem_filter                       exhaustive
% 3.65/0.99  --prep_sem_filter_out                   false
% 3.65/0.99  --pred_elim                             true
% 3.65/0.99  --res_sim_input                         true
% 3.65/0.99  --eq_ax_congr_red                       true
% 3.65/0.99  --pure_diseq_elim                       true
% 3.65/0.99  --brand_transform                       false
% 3.65/0.99  --non_eq_to_eq                          false
% 3.65/0.99  --prep_def_merge                        true
% 3.65/0.99  --prep_def_merge_prop_impl              false
% 3.65/0.99  --prep_def_merge_mbd                    true
% 3.65/0.99  --prep_def_merge_tr_red                 false
% 3.65/0.99  --prep_def_merge_tr_cl                  false
% 3.65/0.99  --smt_preprocessing                     true
% 3.65/0.99  --smt_ac_axioms                         fast
% 3.65/0.99  --preprocessed_out                      false
% 3.65/0.99  --preprocessed_stats                    false
% 3.65/0.99  
% 3.65/0.99  ------ Abstraction refinement Options
% 3.65/0.99  
% 3.65/0.99  --abstr_ref                             []
% 3.65/0.99  --abstr_ref_prep                        false
% 3.65/0.99  --abstr_ref_until_sat                   false
% 3.65/0.99  --abstr_ref_sig_restrict                funpre
% 3.65/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/0.99  --abstr_ref_under                       []
% 3.65/0.99  
% 3.65/0.99  ------ SAT Options
% 3.65/0.99  
% 3.65/0.99  --sat_mode                              false
% 3.65/0.99  --sat_fm_restart_options                ""
% 3.65/0.99  --sat_gr_def                            false
% 3.65/0.99  --sat_epr_types                         true
% 3.65/0.99  --sat_non_cyclic_types                  false
% 3.65/0.99  --sat_finite_models                     false
% 3.65/0.99  --sat_fm_lemmas                         false
% 3.65/0.99  --sat_fm_prep                           false
% 3.65/0.99  --sat_fm_uc_incr                        true
% 3.65/0.99  --sat_out_model                         small
% 3.65/0.99  --sat_out_clauses                       false
% 3.65/0.99  
% 3.65/0.99  ------ QBF Options
% 3.65/0.99  
% 3.65/0.99  --qbf_mode                              false
% 3.65/0.99  --qbf_elim_univ                         false
% 3.65/0.99  --qbf_dom_inst                          none
% 3.65/0.99  --qbf_dom_pre_inst                      false
% 3.65/0.99  --qbf_sk_in                             false
% 3.65/0.99  --qbf_pred_elim                         true
% 3.65/0.99  --qbf_split                             512
% 3.65/0.99  
% 3.65/0.99  ------ BMC1 Options
% 3.65/0.99  
% 3.65/0.99  --bmc1_incremental                      false
% 3.65/0.99  --bmc1_axioms                           reachable_all
% 3.65/0.99  --bmc1_min_bound                        0
% 3.65/0.99  --bmc1_max_bound                        -1
% 3.65/0.99  --bmc1_max_bound_default                -1
% 3.65/0.99  --bmc1_symbol_reachability              true
% 3.65/0.99  --bmc1_property_lemmas                  false
% 3.65/0.99  --bmc1_k_induction                      false
% 3.65/0.99  --bmc1_non_equiv_states                 false
% 3.65/0.99  --bmc1_deadlock                         false
% 3.65/0.99  --bmc1_ucm                              false
% 3.65/0.99  --bmc1_add_unsat_core                   none
% 3.65/0.99  --bmc1_unsat_core_children              false
% 3.65/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/0.99  --bmc1_out_stat                         full
% 3.65/0.99  --bmc1_ground_init                      false
% 3.65/0.99  --bmc1_pre_inst_next_state              false
% 3.65/0.99  --bmc1_pre_inst_state                   false
% 3.65/0.99  --bmc1_pre_inst_reach_state             false
% 3.65/0.99  --bmc1_out_unsat_core                   false
% 3.65/0.99  --bmc1_aig_witness_out                  false
% 3.65/0.99  --bmc1_verbose                          false
% 3.65/0.99  --bmc1_dump_clauses_tptp                false
% 3.65/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.65/0.99  --bmc1_dump_file                        -
% 3.65/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.65/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.65/0.99  --bmc1_ucm_extend_mode                  1
% 3.65/0.99  --bmc1_ucm_init_mode                    2
% 3.65/0.99  --bmc1_ucm_cone_mode                    none
% 3.65/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.65/0.99  --bmc1_ucm_relax_model                  4
% 3.65/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.65/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/0.99  --bmc1_ucm_layered_model                none
% 3.65/0.99  --bmc1_ucm_max_lemma_size               10
% 3.65/0.99  
% 3.65/0.99  ------ AIG Options
% 3.65/0.99  
% 3.65/0.99  --aig_mode                              false
% 3.65/0.99  
% 3.65/0.99  ------ Instantiation Options
% 3.65/0.99  
% 3.65/0.99  --instantiation_flag                    true
% 3.65/0.99  --inst_sos_flag                         false
% 3.65/0.99  --inst_sos_phase                        true
% 3.65/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/0.99  --inst_lit_sel_side                     none
% 3.65/0.99  --inst_solver_per_active                1400
% 3.65/0.99  --inst_solver_calls_frac                1.
% 3.65/0.99  --inst_passive_queue_type               priority_queues
% 3.65/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/0.99  --inst_passive_queues_freq              [25;2]
% 3.65/0.99  --inst_dismatching                      true
% 3.65/0.99  --inst_eager_unprocessed_to_passive     true
% 3.65/0.99  --inst_prop_sim_given                   true
% 3.65/0.99  --inst_prop_sim_new                     false
% 3.65/0.99  --inst_subs_new                         false
% 3.65/0.99  --inst_eq_res_simp                      false
% 3.65/0.99  --inst_subs_given                       false
% 3.65/0.99  --inst_orphan_elimination               true
% 3.65/0.99  --inst_learning_loop_flag               true
% 3.65/0.99  --inst_learning_start                   3000
% 3.65/0.99  --inst_learning_factor                  2
% 3.65/0.99  --inst_start_prop_sim_after_learn       3
% 3.65/0.99  --inst_sel_renew                        solver
% 3.65/0.99  --inst_lit_activity_flag                true
% 3.65/0.99  --inst_restr_to_given                   false
% 3.65/0.99  --inst_activity_threshold               500
% 3.65/0.99  --inst_out_proof                        true
% 3.65/0.99  
% 3.65/0.99  ------ Resolution Options
% 3.65/0.99  
% 3.65/0.99  --resolution_flag                       false
% 3.65/0.99  --res_lit_sel                           adaptive
% 3.65/0.99  --res_lit_sel_side                      none
% 3.65/0.99  --res_ordering                          kbo
% 3.65/0.99  --res_to_prop_solver                    active
% 3.65/0.99  --res_prop_simpl_new                    false
% 3.65/0.99  --res_prop_simpl_given                  true
% 3.65/0.99  --res_passive_queue_type                priority_queues
% 3.65/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/0.99  --res_passive_queues_freq               [15;5]
% 3.65/0.99  --res_forward_subs                      full
% 3.65/0.99  --res_backward_subs                     full
% 3.65/0.99  --res_forward_subs_resolution           true
% 3.65/0.99  --res_backward_subs_resolution          true
% 3.65/0.99  --res_orphan_elimination                true
% 3.65/0.99  --res_time_limit                        2.
% 3.65/0.99  --res_out_proof                         true
% 3.65/0.99  
% 3.65/0.99  ------ Superposition Options
% 3.65/0.99  
% 3.65/0.99  --superposition_flag                    true
% 3.65/0.99  --sup_passive_queue_type                priority_queues
% 3.65/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.65/0.99  --demod_completeness_check              fast
% 3.65/0.99  --demod_use_ground                      true
% 3.65/0.99  --sup_to_prop_solver                    passive
% 3.65/0.99  --sup_prop_simpl_new                    true
% 3.65/0.99  --sup_prop_simpl_given                  true
% 3.65/0.99  --sup_fun_splitting                     false
% 3.65/0.99  --sup_smt_interval                      50000
% 3.65/0.99  
% 3.65/0.99  ------ Superposition Simplification Setup
% 3.65/0.99  
% 3.65/0.99  --sup_indices_passive                   []
% 3.65/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.99  --sup_full_bw                           [BwDemod]
% 3.65/0.99  --sup_immed_triv                        [TrivRules]
% 3.65/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.99  --sup_immed_bw_main                     []
% 3.65/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.99  
% 3.65/0.99  ------ Combination Options
% 3.65/0.99  
% 3.65/0.99  --comb_res_mult                         3
% 3.65/0.99  --comb_sup_mult                         2
% 3.65/0.99  --comb_inst_mult                        10
% 3.65/0.99  
% 3.65/0.99  ------ Debug Options
% 3.65/0.99  
% 3.65/0.99  --dbg_backtrace                         false
% 3.65/0.99  --dbg_dump_prop_clauses                 false
% 3.65/0.99  --dbg_dump_prop_clauses_file            -
% 3.65/0.99  --dbg_out_stat                          false
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  ------ Proving...
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  % SZS status Theorem for theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  fof(f1,axiom,(
% 3.65/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f54,plain,(
% 3.65/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.65/0.99    inference(nnf_transformation,[],[f1])).
% 3.65/0.99  
% 3.65/0.99  fof(f55,plain,(
% 3.65/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.65/0.99    inference(rectify,[],[f54])).
% 3.65/0.99  
% 3.65/0.99  fof(f56,plain,(
% 3.65/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.65/0.99    introduced(choice_axiom,[])).
% 3.65/0.99  
% 3.65/0.99  fof(f57,plain,(
% 3.65/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.65/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f55,f56])).
% 3.65/0.99  
% 3.65/0.99  fof(f70,plain,(
% 3.65/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f57])).
% 3.65/0.99  
% 3.65/0.99  fof(f5,axiom,(
% 3.65/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f26,plain,(
% 3.65/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f5])).
% 3.65/0.99  
% 3.65/0.99  fof(f60,plain,(
% 3.65/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.65/0.99    inference(nnf_transformation,[],[f26])).
% 3.65/0.99  
% 3.65/0.99  fof(f77,plain,(
% 3.65/0.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f60])).
% 3.65/0.99  
% 3.65/0.99  fof(f69,plain,(
% 3.65/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f57])).
% 3.65/0.99  
% 3.65/0.99  fof(f13,axiom,(
% 3.65/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f36,plain,(
% 3.65/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f13])).
% 3.65/0.99  
% 3.65/0.99  fof(f37,plain,(
% 3.65/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.65/0.99    inference(flattening,[],[f36])).
% 3.65/0.99  
% 3.65/0.99  fof(f88,plain,(
% 3.65/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f37])).
% 3.65/0.99  
% 3.65/0.99  fof(f21,conjecture,(
% 3.65/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f22,negated_conjecture,(
% 3.65/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.65/0.99    inference(negated_conjecture,[],[f21])).
% 3.65/0.99  
% 3.65/0.99  fof(f52,plain,(
% 3.65/0.99    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f22])).
% 3.65/0.99  
% 3.65/0.99  fof(f53,plain,(
% 3.65/0.99    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.65/0.99    inference(flattening,[],[f52])).
% 3.65/0.99  
% 3.65/0.99  fof(f64,plain,(
% 3.65/0.99    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.65/0.99    inference(nnf_transformation,[],[f53])).
% 3.65/0.99  
% 3.65/0.99  fof(f65,plain,(
% 3.65/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.65/0.99    inference(flattening,[],[f64])).
% 3.65/0.99  
% 3.65/0.99  fof(f67,plain,(
% 3.65/0.99    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK3) | ~v2_tex_2(sK3,X0)) & (v1_zfmisc_1(sK3) | v2_tex_2(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK3))) )),
% 3.65/0.99    introduced(choice_axiom,[])).
% 3.65/0.99  
% 3.65/0.99  fof(f66,plain,(
% 3.65/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK2)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.65/0.99    introduced(choice_axiom,[])).
% 3.65/0.99  
% 3.65/0.99  fof(f68,plain,(
% 3.65/0.99    ((~v1_zfmisc_1(sK3) | ~v2_tex_2(sK3,sK2)) & (v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.65/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f65,f67,f66])).
% 3.65/0.99  
% 3.65/0.99  fof(f105,plain,(
% 3.65/0.99    ~v1_xboole_0(sK3)),
% 3.65/0.99    inference(cnf_transformation,[],[f68])).
% 3.65/0.99  
% 3.65/0.99  fof(f12,axiom,(
% 3.65/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f34,plain,(
% 3.65/0.99    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f12])).
% 3.65/0.99  
% 3.65/0.99  fof(f35,plain,(
% 3.65/0.99    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.65/0.99    inference(flattening,[],[f34])).
% 3.65/0.99  
% 3.65/0.99  fof(f87,plain,(
% 3.65/0.99    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f35])).
% 3.65/0.99  
% 3.65/0.99  fof(f7,axiom,(
% 3.65/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f61,plain,(
% 3.65/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.65/0.99    inference(nnf_transformation,[],[f7])).
% 3.65/0.99  
% 3.65/0.99  fof(f81,plain,(
% 3.65/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.65/0.99    inference(cnf_transformation,[],[f61])).
% 3.65/0.99  
% 3.65/0.99  fof(f18,axiom,(
% 3.65/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f46,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 3.65/0.99    inference(ennf_transformation,[],[f18])).
% 3.65/0.99  
% 3.65/0.99  fof(f47,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.65/0.99    inference(flattening,[],[f46])).
% 3.65/0.99  
% 3.65/0.99  fof(f95,plain,(
% 3.65/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f47])).
% 3.65/0.99  
% 3.65/0.99  fof(f82,plain,(
% 3.65/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f61])).
% 3.65/0.99  
% 3.65/0.99  fof(f6,axiom,(
% 3.65/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f27,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.65/0.99    inference(ennf_transformation,[],[f6])).
% 3.65/0.99  
% 3.65/0.99  fof(f80,plain,(
% 3.65/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f27])).
% 3.65/0.99  
% 3.65/0.99  fof(f107,plain,(
% 3.65/0.99    v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2)),
% 3.65/0.99    inference(cnf_transformation,[],[f68])).
% 3.65/0.99  
% 3.65/0.99  fof(f106,plain,(
% 3.65/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.65/0.99    inference(cnf_transformation,[],[f68])).
% 3.65/0.99  
% 3.65/0.99  fof(f19,axiom,(
% 3.65/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f23,plain,(
% 3.65/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.65/0.99    inference(pure_predicate_removal,[],[f19])).
% 3.65/0.99  
% 3.65/0.99  fof(f48,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f23])).
% 3.65/0.99  
% 3.65/0.99  fof(f49,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.65/0.99    inference(flattening,[],[f48])).
% 3.65/0.99  
% 3.65/0.99  fof(f62,plain,(
% 3.65/0.99    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & v1_tdlat_3(sK1(X0,X1)) & ~v2_struct_0(sK1(X0,X1))))),
% 3.65/0.99    introduced(choice_axiom,[])).
% 3.65/0.99  
% 3.65/0.99  fof(f63,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : ((u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & v1_tdlat_3(sK1(X0,X1)) & ~v2_struct_0(sK1(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.65/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f62])).
% 3.65/0.99  
% 3.65/0.99  fof(f98,plain,(
% 3.65/0.99    ( ! [X0,X1] : (m1_pre_topc(sK1(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f63])).
% 3.65/0.99  
% 3.65/0.99  fof(f101,plain,(
% 3.65/0.99    ~v2_struct_0(sK2)),
% 3.65/0.99    inference(cnf_transformation,[],[f68])).
% 3.65/0.99  
% 3.65/0.99  fof(f102,plain,(
% 3.65/0.99    v2_pre_topc(sK2)),
% 3.65/0.99    inference(cnf_transformation,[],[f68])).
% 3.65/0.99  
% 3.65/0.99  fof(f104,plain,(
% 3.65/0.99    l1_pre_topc(sK2)),
% 3.65/0.99    inference(cnf_transformation,[],[f68])).
% 3.65/0.99  
% 3.65/0.99  fof(f10,axiom,(
% 3.65/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f31,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.65/0.99    inference(ennf_transformation,[],[f10])).
% 3.65/0.99  
% 3.65/0.99  fof(f85,plain,(
% 3.65/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f31])).
% 3.65/0.99  
% 3.65/0.99  fof(f103,plain,(
% 3.65/0.99    v2_tdlat_3(sK2)),
% 3.65/0.99    inference(cnf_transformation,[],[f68])).
% 3.65/0.99  
% 3.65/0.99  fof(f108,plain,(
% 3.65/0.99    ~v1_zfmisc_1(sK3) | ~v2_tex_2(sK3,sK2)),
% 3.65/0.99    inference(cnf_transformation,[],[f68])).
% 3.65/0.99  
% 3.65/0.99  fof(f2,axiom,(
% 3.65/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f58,plain,(
% 3.65/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.65/0.99    inference(nnf_transformation,[],[f2])).
% 3.65/0.99  
% 3.65/0.99  fof(f59,plain,(
% 3.65/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.65/0.99    inference(flattening,[],[f58])).
% 3.65/0.99  
% 3.65/0.99  fof(f71,plain,(
% 3.65/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.65/0.99    inference(cnf_transformation,[],[f59])).
% 3.65/0.99  
% 3.65/0.99  fof(f110,plain,(
% 3.65/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.65/0.99    inference(equality_resolution,[],[f71])).
% 3.65/0.99  
% 3.65/0.99  fof(f16,axiom,(
% 3.65/0.99    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f42,plain,(
% 3.65/0.99    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.65/0.99    inference(ennf_transformation,[],[f16])).
% 3.65/0.99  
% 3.65/0.99  fof(f43,plain,(
% 3.65/0.99    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.65/0.99    inference(flattening,[],[f42])).
% 3.65/0.99  
% 3.65/0.99  fof(f92,plain,(
% 3.65/0.99    ( ! [X0] : (v7_struct_0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f43])).
% 3.65/0.99  
% 3.65/0.99  fof(f15,axiom,(
% 3.65/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f40,plain,(
% 3.65/0.99    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.65/0.99    inference(ennf_transformation,[],[f15])).
% 3.65/0.99  
% 3.65/0.99  fof(f41,plain,(
% 3.65/0.99    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.65/0.99    inference(flattening,[],[f40])).
% 3.65/0.99  
% 3.65/0.99  fof(f90,plain,(
% 3.65/0.99    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f41])).
% 3.65/0.99  
% 3.65/0.99  fof(f9,axiom,(
% 3.65/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f30,plain,(
% 3.65/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.65/0.99    inference(ennf_transformation,[],[f9])).
% 3.65/0.99  
% 3.65/0.99  fof(f84,plain,(
% 3.65/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f30])).
% 3.65/0.99  
% 3.65/0.99  fof(f11,axiom,(
% 3.65/0.99    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f32,plain,(
% 3.65/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f11])).
% 3.65/0.99  
% 3.65/0.99  fof(f33,plain,(
% 3.65/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 3.65/0.99    inference(flattening,[],[f32])).
% 3.65/0.99  
% 3.65/0.99  fof(f86,plain,(
% 3.65/0.99    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f33])).
% 3.65/0.99  
% 3.65/0.99  fof(f73,plain,(
% 3.65/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f59])).
% 3.65/0.99  
% 3.65/0.99  fof(f97,plain,(
% 3.65/0.99    ( ! [X0,X1] : (v1_tdlat_3(sK1(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f63])).
% 3.65/0.99  
% 3.65/0.99  fof(f99,plain,(
% 3.65/0.99    ( ! [X0,X1] : (u1_struct_0(sK1(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f63])).
% 3.65/0.99  
% 3.65/0.99  fof(f96,plain,(
% 3.65/0.99    ( ! [X0,X1] : (~v2_struct_0(sK1(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f63])).
% 3.65/0.99  
% 3.65/0.99  fof(f17,axiom,(
% 3.65/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f44,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f17])).
% 3.65/0.99  
% 3.65/0.99  fof(f45,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.65/0.99    inference(flattening,[],[f44])).
% 3.65/0.99  
% 3.65/0.99  fof(f94,plain,(
% 3.65/0.99    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f45])).
% 3.65/0.99  
% 3.65/0.99  fof(f4,axiom,(
% 3.65/0.99    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f75,plain,(
% 3.65/0.99    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.65/0.99    inference(cnf_transformation,[],[f4])).
% 3.65/0.99  
% 3.65/0.99  fof(f76,plain,(
% 3.65/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f60])).
% 3.65/0.99  
% 3.65/0.99  fof(f8,axiom,(
% 3.65/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f28,plain,(
% 3.65/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.65/0.99    inference(ennf_transformation,[],[f8])).
% 3.65/0.99  
% 3.65/0.99  fof(f29,plain,(
% 3.65/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.65/0.99    inference(flattening,[],[f28])).
% 3.65/0.99  
% 3.65/0.99  fof(f83,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f29])).
% 3.65/0.99  
% 3.65/0.99  fof(f20,axiom,(
% 3.65/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f50,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f20])).
% 3.65/0.99  
% 3.65/0.99  fof(f51,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.65/0.99    inference(flattening,[],[f50])).
% 3.65/0.99  
% 3.65/0.99  fof(f100,plain,(
% 3.65/0.99    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f51])).
% 3.65/0.99  
% 3.65/0.99  cnf(c_0,plain,
% 3.65/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_9,plain,
% 3.65/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.65/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1,plain,
% 3.65/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.65/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_243,plain,
% 3.65/0.99      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.65/0.99      inference(global_propositional_subsumption,[status(thm)],[c_9,c_1]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_244,plain,
% 3.65/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.65/0.99      inference(renaming,[status(thm)],[c_243]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_551,plain,
% 3.65/0.99      ( m1_subset_1(X0,X1) | v1_xboole_0(X2) | X1 != X2 | sK0(X2) != X0 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_244]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_552,plain,
% 3.65/0.99      ( m1_subset_1(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_551]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4020,plain,
% 3.65/0.99      ( m1_subset_1(sK0(X0),X0) = iProver_top
% 3.65/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_552]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_19,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,X1)
% 3.65/0.99      | v1_xboole_0(X1)
% 3.65/0.99      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4039,plain,
% 3.65/0.99      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 3.65/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.65/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6852,plain,
% 3.65/0.99      ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
% 3.65/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_4020,c_4039]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_35,negated_conjecture,
% 3.65/0.99      ( ~ v1_xboole_0(sK3) ),
% 3.65/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4028,plain,
% 3.65/0.99      ( v1_xboole_0(sK3) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7295,plain,
% 3.65/0.99      ( k6_domain_1(sK3,sK0(sK3)) = k1_tarski(sK0(sK3)) ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_6852,c_4028]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_18,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,X1)
% 3.65/0.99      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 3.65/0.99      | v1_xboole_0(X1) ),
% 3.65/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4040,plain,
% 3.65/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.65/0.99      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 3.65/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7507,plain,
% 3.65/0.99      ( m1_subset_1(k1_tarski(sK0(sK3)),k1_zfmisc_1(sK3)) = iProver_top
% 3.65/0.99      | m1_subset_1(sK0(sK3),sK3) != iProver_top
% 3.65/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_7295,c_4040]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_44,plain,
% 3.65/0.99      ( v1_xboole_0(sK3) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4339,plain,
% 3.65/0.99      ( m1_subset_1(sK0(sK3),sK3) | v1_xboole_0(sK3) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_552]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4340,plain,
% 3.65/0.99      ( m1_subset_1(sK0(sK3),sK3) = iProver_top
% 3.65/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_4339]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7740,plain,
% 3.65/0.99      ( m1_subset_1(k1_tarski(sK0(sK3)),k1_zfmisc_1(sK3)) = iProver_top ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_7507,c_44,c_4340]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_13,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.65/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4042,plain,
% 3.65/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.65/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7746,plain,
% 3.65/0.99      ( r1_tarski(k1_tarski(sK0(sK3)),sK3) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_7740,c_4042]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_26,plain,
% 3.65/0.99      ( ~ r1_tarski(X0,X1)
% 3.65/0.99      | ~ v1_zfmisc_1(X1)
% 3.65/0.99      | v1_xboole_0(X0)
% 3.65/0.99      | v1_xboole_0(X1)
% 3.65/0.99      | X1 = X0 ),
% 3.65/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_12,plain,
% 3.65/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.65/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_11,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/0.99      | ~ v1_xboole_0(X1)
% 3.65/0.99      | v1_xboole_0(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_218,plain,
% 3.65/0.99      ( v1_xboole_0(X0)
% 3.65/0.99      | ~ v1_zfmisc_1(X1)
% 3.65/0.99      | ~ r1_tarski(X0,X1)
% 3.65/0.99      | X1 = X0 ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_26,c_12,c_11]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_219,plain,
% 3.65/0.99      ( ~ r1_tarski(X0,X1)
% 3.65/0.99      | ~ v1_zfmisc_1(X1)
% 3.65/0.99      | v1_xboole_0(X0)
% 3.65/0.99      | X1 = X0 ),
% 3.65/0.99      inference(renaming,[status(thm)],[c_218]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4023,plain,
% 3.65/0.99      ( X0 = X1
% 3.65/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.65/0.99      | v1_zfmisc_1(X0) != iProver_top
% 3.65/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_219]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_8957,plain,
% 3.65/0.99      ( k1_tarski(sK0(sK3)) = sK3
% 3.65/0.99      | v1_zfmisc_1(sK3) != iProver_top
% 3.65/0.99      | v1_xboole_0(k1_tarski(sK0(sK3))) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_7746,c_4023]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_33,negated_conjecture,
% 3.65/0.99      ( v2_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 3.65/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_46,plain,
% 3.65/0.99      ( v2_tex_2(sK3,sK2) = iProver_top
% 3.65/0.99      | v1_zfmisc_1(sK3) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_34,negated_conjecture,
% 3.65/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.65/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4029,plain,
% 3.65/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_28,plain,
% 3.65/0.99      ( ~ v2_tex_2(X0,X1)
% 3.65/0.99      | m1_pre_topc(sK1(X1,X0),X1)
% 3.65/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.99      | v2_struct_0(X1)
% 3.65/0.99      | ~ v2_pre_topc(X1)
% 3.65/0.99      | ~ l1_pre_topc(X1)
% 3.65/0.99      | v1_xboole_0(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4035,plain,
% 3.65/0.99      ( v2_tex_2(X0,X1) != iProver_top
% 3.65/0.99      | m1_pre_topc(sK1(X1,X0),X1) = iProver_top
% 3.65/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.65/0.99      | v2_struct_0(X1) = iProver_top
% 3.65/0.99      | v2_pre_topc(X1) != iProver_top
% 3.65/0.99      | l1_pre_topc(X1) != iProver_top
% 3.65/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7072,plain,
% 3.65/0.99      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.65/0.99      | m1_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
% 3.65/0.99      | v2_struct_0(sK2) = iProver_top
% 3.65/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.65/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.65/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_4029,c_4035]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_39,negated_conjecture,
% 3.65/0.99      ( ~ v2_struct_0(sK2) ),
% 3.65/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_40,plain,
% 3.65/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_38,negated_conjecture,
% 3.65/0.99      ( v2_pre_topc(sK2) ),
% 3.65/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_41,plain,
% 3.65/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_36,negated_conjecture,
% 3.65/0.99      ( l1_pre_topc(sK2) ),
% 3.65/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_43,plain,
% 3.65/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7582,plain,
% 3.65/0.99      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.65/0.99      | m1_pre_topc(sK1(sK2,sK3),sK2) = iProver_top ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_7072,c_40,c_41,c_43,c_44]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_16,plain,
% 3.65/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4041,plain,
% 3.65/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.65/0.99      | l1_pre_topc(X1) != iProver_top
% 3.65/0.99      | l1_pre_topc(X0) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7589,plain,
% 3.65/0.99      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.65/0.99      | l1_pre_topc(sK1(sK2,sK3)) = iProver_top
% 3.65/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_7582,c_4041]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_37,negated_conjecture,
% 3.65/0.99      ( v2_tdlat_3(sK2) ),
% 3.65/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_42,plain,
% 3.65/0.99      ( v2_tdlat_3(sK2) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_32,negated_conjecture,
% 3.65/0.99      ( ~ v2_tex_2(sK3,sK2) | ~ v1_zfmisc_1(sK3) ),
% 3.65/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_47,plain,
% 3.65/0.99      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.65/0.99      | v1_zfmisc_1(sK3) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4,plain,
% 3.65/0.99      ( r1_tarski(X0,X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4559,plain,
% 3.65/0.99      ( r1_tarski(sK3,sK3) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_23,plain,
% 3.65/0.99      ( v2_struct_0(X0)
% 3.65/0.99      | ~ v2_tdlat_3(X0)
% 3.65/0.99      | ~ v1_tdlat_3(X0)
% 3.65/0.99      | ~ v2_pre_topc(X0)
% 3.65/0.99      | v7_struct_0(X0)
% 3.65/0.99      | ~ l1_pre_topc(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_21,plain,
% 3.65/0.99      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_224,plain,
% 3.65/0.99      ( ~ v1_tdlat_3(X0)
% 3.65/0.99      | ~ v2_tdlat_3(X0)
% 3.65/0.99      | v2_struct_0(X0)
% 3.65/0.99      | v7_struct_0(X0)
% 3.65/0.99      | ~ l1_pre_topc(X0) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_23,c_21]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_225,plain,
% 3.65/0.99      ( v2_struct_0(X0)
% 3.65/0.99      | ~ v2_tdlat_3(X0)
% 3.65/0.99      | ~ v1_tdlat_3(X0)
% 3.65/0.99      | v7_struct_0(X0)
% 3.65/0.99      | ~ l1_pre_topc(X0) ),
% 3.65/0.99      inference(renaming,[status(thm)],[c_224]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_15,plain,
% 3.65/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_17,plain,
% 3.65/0.99      ( ~ v7_struct_0(X0)
% 3.65/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.65/0.99      | ~ l1_struct_0(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_505,plain,
% 3.65/0.99      ( ~ v7_struct_0(X0)
% 3.65/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.65/0.99      | ~ l1_pre_topc(X0) ),
% 3.65/0.99      inference(resolution,[status(thm)],[c_15,c_17]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_523,plain,
% 3.65/0.99      ( v2_struct_0(X0)
% 3.65/0.99      | ~ v2_tdlat_3(X0)
% 3.65/0.99      | ~ v1_tdlat_3(X0)
% 3.65/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.65/0.99      | ~ l1_pre_topc(X0) ),
% 3.65/0.99      inference(resolution,[status(thm)],[c_225,c_505]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4641,plain,
% 3.65/0.99      ( v2_struct_0(sK1(X0,sK3))
% 3.65/0.99      | ~ v2_tdlat_3(sK1(X0,sK3))
% 3.65/0.99      | ~ v1_tdlat_3(sK1(X0,sK3))
% 3.65/0.99      | v1_zfmisc_1(u1_struct_0(sK1(X0,sK3)))
% 3.65/0.99      | ~ l1_pre_topc(sK1(X0,sK3)) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_523]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4642,plain,
% 3.65/0.99      ( v2_struct_0(sK1(X0,sK3)) = iProver_top
% 3.65/0.99      | v2_tdlat_3(sK1(X0,sK3)) != iProver_top
% 3.65/0.99      | v1_tdlat_3(sK1(X0,sK3)) != iProver_top
% 3.65/0.99      | v1_zfmisc_1(u1_struct_0(sK1(X0,sK3))) = iProver_top
% 3.65/0.99      | l1_pre_topc(sK1(X0,sK3)) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_4641]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4644,plain,
% 3.65/0.99      ( v2_struct_0(sK1(sK2,sK3)) = iProver_top
% 3.65/0.99      | v2_tdlat_3(sK1(sK2,sK3)) != iProver_top
% 3.65/0.99      | v1_tdlat_3(sK1(sK2,sK3)) != iProver_top
% 3.65/0.99      | v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3))) = iProver_top
% 3.65/0.99      | l1_pre_topc(sK1(sK2,sK3)) != iProver_top ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_4642]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_2,plain,
% 3.65/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.65/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4526,plain,
% 3.65/0.99      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4763,plain,
% 3.65/0.99      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_4526]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3209,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4525,plain,
% 3.65/0.99      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_3209]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4776,plain,
% 3.65/0.99      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_4525]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5206,plain,
% 3.65/0.99      ( u1_struct_0(sK1(X0,sK3)) != sK3
% 3.65/0.99      | sK3 = u1_struct_0(sK1(X0,sK3))
% 3.65/0.99      | sK3 != sK3 ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_4776]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5207,plain,
% 3.65/0.99      ( u1_struct_0(sK1(sK2,sK3)) != sK3
% 3.65/0.99      | sK3 = u1_struct_0(sK1(sK2,sK3))
% 3.65/0.99      | sK3 != sK3 ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_5206]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3216,plain,
% 3.65/0.99      ( ~ v1_zfmisc_1(X0) | v1_zfmisc_1(X1) | X1 != X0 ),
% 3.65/0.99      theory(equality) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5053,plain,
% 3.65/0.99      ( v1_zfmisc_1(X0)
% 3.65/0.99      | ~ v1_zfmisc_1(u1_struct_0(sK1(X1,sK3)))
% 3.65/0.99      | X0 != u1_struct_0(sK1(X1,sK3)) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_3216]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5696,plain,
% 3.65/0.99      ( ~ v1_zfmisc_1(u1_struct_0(sK1(X0,sK3)))
% 3.65/0.99      | v1_zfmisc_1(sK3)
% 3.65/0.99      | sK3 != u1_struct_0(sK1(X0,sK3)) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_5053]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5697,plain,
% 3.65/0.99      ( sK3 != u1_struct_0(sK1(X0,sK3))
% 3.65/0.99      | v1_zfmisc_1(u1_struct_0(sK1(X0,sK3))) != iProver_top
% 3.65/0.99      | v1_zfmisc_1(sK3) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_5696]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5699,plain,
% 3.65/0.99      ( sK3 != u1_struct_0(sK1(sK2,sK3))
% 3.65/0.99      | v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3))) != iProver_top
% 3.65/0.99      | v1_zfmisc_1(sK3) = iProver_top ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_5697]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_29,plain,
% 3.65/0.99      ( ~ v2_tex_2(X0,X1)
% 3.65/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.99      | v2_struct_0(X1)
% 3.65/0.99      | v1_tdlat_3(sK1(X1,X0))
% 3.65/0.99      | ~ v2_pre_topc(X1)
% 3.65/0.99      | ~ l1_pre_topc(X1)
% 3.65/0.99      | v1_xboole_0(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4034,plain,
% 3.65/0.99      ( v2_tex_2(X0,X1) != iProver_top
% 3.65/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.65/0.99      | v2_struct_0(X1) = iProver_top
% 3.65/0.99      | v1_tdlat_3(sK1(X1,X0)) = iProver_top
% 3.65/0.99      | v2_pre_topc(X1) != iProver_top
% 3.65/0.99      | l1_pre_topc(X1) != iProver_top
% 3.65/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6070,plain,
% 3.65/0.99      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.65/0.99      | v2_struct_0(sK2) = iProver_top
% 3.65/0.99      | v1_tdlat_3(sK1(sK2,sK3)) = iProver_top
% 3.65/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.65/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.65/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_4029,c_4034]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6438,plain,
% 3.65/0.99      ( v1_tdlat_3(sK1(sK2,sK3)) = iProver_top
% 3.65/0.99      | v2_tex_2(sK3,sK2) != iProver_top ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_6070,c_40,c_41,c_43,c_44]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6439,plain,
% 3.65/0.99      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.65/0.99      | v1_tdlat_3(sK1(sK2,sK3)) = iProver_top ),
% 3.65/0.99      inference(renaming,[status(thm)],[c_6438]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_27,plain,
% 3.65/0.99      ( ~ v2_tex_2(X0,X1)
% 3.65/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.99      | v2_struct_0(X1)
% 3.65/0.99      | ~ v2_pre_topc(X1)
% 3.65/0.99      | ~ l1_pre_topc(X1)
% 3.65/0.99      | v1_xboole_0(X0)
% 3.65/0.99      | u1_struct_0(sK1(X1,X0)) = X0 ),
% 3.65/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4036,plain,
% 3.65/0.99      ( u1_struct_0(sK1(X0,X1)) = X1
% 3.65/0.99      | v2_tex_2(X1,X0) != iProver_top
% 3.65/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.99      | v2_struct_0(X0) = iProver_top
% 3.65/0.99      | v2_pre_topc(X0) != iProver_top
% 3.65/0.99      | l1_pre_topc(X0) != iProver_top
% 3.65/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6255,plain,
% 3.65/0.99      ( u1_struct_0(sK1(sK2,sK3)) = sK3
% 3.65/0.99      | v2_tex_2(sK3,sK2) != iProver_top
% 3.65/0.99      | v2_struct_0(sK2) = iProver_top
% 3.65/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.65/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.65/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_4029,c_4036]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6445,plain,
% 3.65/0.99      ( u1_struct_0(sK1(sK2,sK3)) = sK3
% 3.65/0.99      | v2_tex_2(sK3,sK2) != iProver_top ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_6255,c_40,c_41,c_43,c_44]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_30,plain,
% 3.65/0.99      ( ~ v2_tex_2(X0,X1)
% 3.65/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.99      | v2_struct_0(X1)
% 3.65/0.99      | ~ v2_struct_0(sK1(X1,X0))
% 3.65/0.99      | ~ v2_pre_topc(X1)
% 3.65/0.99      | ~ l1_pre_topc(X1)
% 3.65/0.99      | v1_xboole_0(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4033,plain,
% 3.65/0.99      ( v2_tex_2(X0,X1) != iProver_top
% 3.65/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.65/0.99      | v2_struct_0(X1) = iProver_top
% 3.65/0.99      | v2_struct_0(sK1(X1,X0)) != iProver_top
% 3.65/0.99      | v2_pre_topc(X1) != iProver_top
% 3.65/0.99      | l1_pre_topc(X1) != iProver_top
% 3.65/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6973,plain,
% 3.65/0.99      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.65/0.99      | v2_struct_0(sK1(sK2,sK3)) != iProver_top
% 3.65/0.99      | v2_struct_0(sK2) = iProver_top
% 3.65/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.65/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.65/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_4029,c_4033]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7510,plain,
% 3.65/0.99      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.65/0.99      | v2_struct_0(sK1(sK2,sK3)) != iProver_top ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_6973,c_40,c_41,c_43,c_44]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_25,plain,
% 3.65/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.65/0.99      | v2_struct_0(X1)
% 3.65/0.99      | ~ v2_tdlat_3(X1)
% 3.65/0.99      | v2_tdlat_3(X0)
% 3.65/0.99      | ~ v2_pre_topc(X1)
% 3.65/0.99      | ~ l1_pre_topc(X1) ),
% 3.65/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1226,plain,
% 3.65/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.65/0.99      | v2_struct_0(X1)
% 3.65/0.99      | ~ v2_tdlat_3(X2)
% 3.65/0.99      | ~ v2_tdlat_3(X1)
% 3.65/0.99      | v2_tdlat_3(X0)
% 3.65/0.99      | ~ l1_pre_topc(X2)
% 3.65/0.99      | ~ l1_pre_topc(X1)
% 3.65/0.99      | X1 != X2 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1227,plain,
% 3.65/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.65/0.99      | v2_struct_0(X1)
% 3.65/0.99      | ~ v2_tdlat_3(X1)
% 3.65/0.99      | v2_tdlat_3(X0)
% 3.65/0.99      | ~ l1_pre_topc(X1) ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_1226]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4018,plain,
% 3.65/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.65/0.99      | v2_struct_0(X1) = iProver_top
% 3.65/0.99      | v2_tdlat_3(X1) != iProver_top
% 3.65/0.99      | v2_tdlat_3(X0) = iProver_top
% 3.65/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_1227]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7588,plain,
% 3.65/0.99      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.65/0.99      | v2_struct_0(sK2) = iProver_top
% 3.65/0.99      | v2_tdlat_3(sK1(sK2,sK3)) = iProver_top
% 3.65/0.99      | v2_tdlat_3(sK2) != iProver_top
% 3.65/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_7582,c_4018]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7672,plain,
% 3.65/0.99      ( v2_tex_2(sK3,sK2) != iProver_top ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_7589,c_40,c_42,c_43,c_47,c_4559,c_4644,c_4763,c_5207,
% 3.65/0.99                 c_5699,c_6439,c_6445,c_7510,c_7588]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_9620,plain,
% 3.65/0.99      ( k1_tarski(sK0(sK3)) = sK3
% 3.65/0.99      | v1_xboole_0(k1_tarski(sK0(sK3))) = iProver_top ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_8957,c_40,c_42,c_43,c_46,c_47,c_4559,c_4644,c_4763,
% 3.65/0.99                 c_5207,c_5699,c_6439,c_6445,c_7510,c_7588,c_7589]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6,plain,
% 3.65/0.99      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 3.65/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4046,plain,
% 3.65/0.99      ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_9626,plain,
% 3.65/0.99      ( k1_tarski(sK0(sK3)) = sK3 ),
% 3.65/0.99      inference(forward_subsumption_resolution,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_9620,c_4046]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_10,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.65/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_14,plain,
% 3.65/0.99      ( m1_subset_1(X0,X1)
% 3.65/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.65/0.99      | ~ r2_hidden(X0,X2) ),
% 3.65/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_580,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,X1)
% 3.65/0.99      | m1_subset_1(X2,X3)
% 3.65/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
% 3.65/0.99      | v1_xboole_0(X1)
% 3.65/0.99      | X2 != X0
% 3.65/0.99      | X4 != X1 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_581,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,X1)
% 3.65/0.99      | m1_subset_1(X0,X2)
% 3.65/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.65/0.99      | v1_xboole_0(X1) ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_580]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4019,plain,
% 3.65/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.65/0.99      | m1_subset_1(X0,X2) = iProver_top
% 3.65/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.65/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_581]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5812,plain,
% 3.65/0.99      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 3.65/0.99      | m1_subset_1(X0,sK3) != iProver_top
% 3.65/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_4029,c_4019]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6326,plain,
% 3.65/0.99      ( m1_subset_1(X0,sK3) != iProver_top
% 3.65/0.99      | m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_5812,c_44]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6327,plain,
% 3.65/0.99      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 3.65/0.99      | m1_subset_1(X0,sK3) != iProver_top ),
% 3.65/0.99      inference(renaming,[status(thm)],[c_6326]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6335,plain,
% 3.65/0.99      ( k6_domain_1(u1_struct_0(sK2),X0) = k1_tarski(X0)
% 3.65/0.99      | m1_subset_1(X0,sK3) != iProver_top
% 3.65/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_6327,c_4039]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4602,plain,
% 3.65/0.99      ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_4029,c_4042]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_305,plain,
% 3.65/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.65/0.99      inference(prop_impl,[status(thm)],[c_12]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_306,plain,
% 3.65/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.65/0.99      inference(renaming,[status(thm)],[c_305]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_372,plain,
% 3.65/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.65/0.99      inference(bin_hyper_res,[status(thm)],[c_11,c_306]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4022,plain,
% 3.65/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.65/0.99      | v1_xboole_0(X1) != iProver_top
% 3.65/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4922,plain,
% 3.65/0.99      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 3.65/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_4602,c_4022]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6491,plain,
% 3.65/0.99      ( m1_subset_1(X0,sK3) != iProver_top
% 3.65/0.99      | k6_domain_1(u1_struct_0(sK2),X0) = k1_tarski(X0) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_6335,c_44,c_4922]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6492,plain,
% 3.65/0.99      ( k6_domain_1(u1_struct_0(sK2),X0) = k1_tarski(X0)
% 3.65/0.99      | m1_subset_1(X0,sK3) != iProver_top ),
% 3.65/0.99      inference(renaming,[status(thm)],[c_6491]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6854,plain,
% 3.65/0.99      ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3))
% 3.65/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_4020,c_6492]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4430,plain,
% 3.65/0.99      ( m1_subset_1(X0,X1)
% 3.65/0.99      | ~ m1_subset_1(X0,sK3)
% 3.65/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
% 3.65/0.99      | v1_xboole_0(sK3) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_581]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4581,plain,
% 3.65/0.99      ( m1_subset_1(X0,u1_struct_0(X1))
% 3.65/0.99      | ~ m1_subset_1(X0,sK3)
% 3.65/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.99      | v1_xboole_0(sK3) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_4430]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4867,plain,
% 3.65/0.99      ( m1_subset_1(sK0(sK3),u1_struct_0(X0))
% 3.65/0.99      | ~ m1_subset_1(sK0(sK3),sK3)
% 3.65/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.65/0.99      | v1_xboole_0(sK3) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_4581]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4869,plain,
% 3.65/0.99      ( m1_subset_1(sK0(sK3),u1_struct_0(sK2))
% 3.65/0.99      | ~ m1_subset_1(sK0(sK3),sK3)
% 3.65/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.99      | v1_xboole_0(sK3) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_4867]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4927,plain,
% 3.65/0.99      ( ~ v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(sK3) ),
% 3.65/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4922]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4838,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.65/0.99      | v1_xboole_0(u1_struct_0(X1))
% 3.65/0.99      | k6_domain_1(u1_struct_0(X1),X0) = k1_tarski(X0) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6160,plain,
% 3.65/0.99      ( ~ m1_subset_1(sK0(sK3),u1_struct_0(X0))
% 3.65/0.99      | v1_xboole_0(u1_struct_0(X0))
% 3.65/0.99      | k6_domain_1(u1_struct_0(X0),sK0(sK3)) = k1_tarski(sK0(sK3)) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_4838]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6162,plain,
% 3.65/0.99      ( ~ m1_subset_1(sK0(sK3),u1_struct_0(sK2))
% 3.65/0.99      | v1_xboole_0(u1_struct_0(sK2))
% 3.65/0.99      | k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3)) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_6160]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_8157,plain,
% 3.65/0.99      ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3)) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_6854,c_35,c_34,c_4339,c_4869,c_4927,c_6162]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_9629,plain,
% 3.65/0.99      ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = sK3 ),
% 3.65/0.99      inference(demodulation,[status(thm)],[c_9626,c_8157]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_31,plain,
% 3.65/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.65/0.99      | v2_struct_0(X0)
% 3.65/0.99      | ~ v2_pre_topc(X0)
% 3.65/0.99      | ~ l1_pre_topc(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4032,plain,
% 3.65/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) = iProver_top
% 3.65/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.65/0.99      | v2_struct_0(X0) = iProver_top
% 3.65/0.99      | v2_pre_topc(X0) != iProver_top
% 3.65/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_10791,plain,
% 3.65/0.99      ( v2_tex_2(sK3,sK2) = iProver_top
% 3.65/0.99      | m1_subset_1(sK0(sK3),u1_struct_0(sK2)) != iProver_top
% 3.65/0.99      | v2_struct_0(sK2) = iProver_top
% 3.65/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.65/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_9629,c_4032]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4868,plain,
% 3.65/0.99      ( m1_subset_1(sK0(sK3),u1_struct_0(X0)) = iProver_top
% 3.65/0.99      | m1_subset_1(sK0(sK3),sK3) != iProver_top
% 3.65/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_4867]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4870,plain,
% 3.65/0.99      ( m1_subset_1(sK0(sK3),u1_struct_0(sK2)) = iProver_top
% 3.65/0.99      | m1_subset_1(sK0(sK3),sK3) != iProver_top
% 3.65/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.65/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_4868]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_45,plain,
% 3.65/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(contradiction,plain,
% 3.65/0.99      ( $false ),
% 3.65/0.99      inference(minisat,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_10791,c_7672,c_4870,c_4340,c_45,c_44,c_43,c_41,c_40]) ).
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  ------                               Statistics
% 3.65/0.99  
% 3.65/0.99  ------ General
% 3.65/0.99  
% 3.65/0.99  abstr_ref_over_cycles:                  0
% 3.65/0.99  abstr_ref_under_cycles:                 0
% 3.65/0.99  gc_basic_clause_elim:                   0
% 3.65/0.99  forced_gc_time:                         0
% 3.65/0.99  parsing_time:                           0.011
% 3.65/0.99  unif_index_cands_time:                  0.
% 3.65/0.99  unif_index_add_time:                    0.
% 3.65/0.99  orderings_time:                         0.
% 3.65/0.99  out_proof_time:                         0.012
% 3.65/0.99  total_time:                             0.256
% 3.65/0.99  num_of_symbols:                         53
% 3.65/0.99  num_of_terms:                           6134
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing
% 3.65/0.99  
% 3.65/0.99  num_of_splits:                          0
% 3.65/0.99  num_of_split_atoms:                     0
% 3.65/0.99  num_of_reused_defs:                     0
% 3.65/0.99  num_eq_ax_congr_red:                    27
% 3.65/0.99  num_of_sem_filtered_clauses:            1
% 3.65/0.99  num_of_subtypes:                        0
% 3.65/0.99  monotx_restored_types:                  0
% 3.65/0.99  sat_num_of_epr_types:                   0
% 3.65/0.99  sat_num_of_non_cyclic_types:            0
% 3.65/0.99  sat_guarded_non_collapsed_types:        0
% 3.65/0.99  num_pure_diseq_elim:                    0
% 3.65/0.99  simp_replaced_by:                       0
% 3.65/0.99  res_preprocessed:                       167
% 3.65/0.99  prep_upred:                             0
% 3.65/0.99  prep_unflattend:                        104
% 3.65/0.99  smt_new_axioms:                         0
% 3.65/0.99  pred_elim_cands:                        11
% 3.65/0.99  pred_elim:                              3
% 3.65/0.99  pred_elim_cl:                           4
% 3.65/0.99  pred_elim_cycles:                       15
% 3.65/0.99  merged_defs:                            16
% 3.65/0.99  merged_defs_ncl:                        0
% 3.65/0.99  bin_hyper_res:                          18
% 3.65/0.99  prep_cycles:                            4
% 3.65/0.99  pred_elim_time:                         0.04
% 3.65/0.99  splitting_time:                         0.
% 3.65/0.99  sem_filter_time:                        0.
% 3.65/0.99  monotx_time:                            0.001
% 3.65/0.99  subtype_inf_time:                       0.
% 3.65/0.99  
% 3.65/0.99  ------ Problem properties
% 3.65/0.99  
% 3.65/0.99  clauses:                                33
% 3.65/0.99  conjectures:                            8
% 3.65/0.99  epr:                                    18
% 3.65/0.99  horn:                                   19
% 3.65/0.99  ground:                                 8
% 3.65/0.99  unary:                                  8
% 3.65/0.99  binary:                                 5
% 3.65/0.99  lits:                                   102
% 3.65/0.99  lits_eq:                                4
% 3.65/0.99  fd_pure:                                0
% 3.65/0.99  fd_pseudo:                              0
% 3.65/0.99  fd_cond:                                0
% 3.65/0.99  fd_pseudo_cond:                         2
% 3.65/0.99  ac_symbols:                             0
% 3.65/0.99  
% 3.65/0.99  ------ Propositional Solver
% 3.65/0.99  
% 3.65/0.99  prop_solver_calls:                      29
% 3.65/0.99  prop_fast_solver_calls:                 1973
% 3.65/0.99  smt_solver_calls:                       0
% 3.65/0.99  smt_fast_solver_calls:                  0
% 3.65/0.99  prop_num_of_clauses:                    3002
% 3.65/0.99  prop_preprocess_simplified:             8631
% 3.65/0.99  prop_fo_subsumed:                       131
% 3.65/0.99  prop_solver_time:                       0.
% 3.65/0.99  smt_solver_time:                        0.
% 3.65/0.99  smt_fast_solver_time:                   0.
% 3.65/0.99  prop_fast_solver_time:                  0.
% 3.65/0.99  prop_unsat_core_time:                   0.
% 3.65/0.99  
% 3.65/0.99  ------ QBF
% 3.65/0.99  
% 3.65/0.99  qbf_q_res:                              0
% 3.65/0.99  qbf_num_tautologies:                    0
% 3.65/0.99  qbf_prep_cycles:                        0
% 3.65/0.99  
% 3.65/0.99  ------ BMC1
% 3.65/0.99  
% 3.65/0.99  bmc1_current_bound:                     -1
% 3.65/0.99  bmc1_last_solved_bound:                 -1
% 3.65/0.99  bmc1_unsat_core_size:                   -1
% 3.65/0.99  bmc1_unsat_core_parents_size:           -1
% 3.65/0.99  bmc1_merge_next_fun:                    0
% 3.65/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.65/0.99  
% 3.65/0.99  ------ Instantiation
% 3.65/0.99  
% 3.65/0.99  inst_num_of_clauses:                    751
% 3.65/0.99  inst_num_in_passive:                    188
% 3.65/0.99  inst_num_in_active:                     448
% 3.65/0.99  inst_num_in_unprocessed:                115
% 3.65/0.99  inst_num_of_loops:                      460
% 3.65/0.99  inst_num_of_learning_restarts:          0
% 3.65/0.99  inst_num_moves_active_passive:          8
% 3.65/0.99  inst_lit_activity:                      0
% 3.65/0.99  inst_lit_activity_moves:                0
% 3.65/0.99  inst_num_tautologies:                   0
% 3.65/0.99  inst_num_prop_implied:                  0
% 3.65/0.99  inst_num_existing_simplified:           0
% 3.65/0.99  inst_num_eq_res_simplified:             0
% 3.65/0.99  inst_num_child_elim:                    0
% 3.65/0.99  inst_num_of_dismatching_blockings:      618
% 3.65/0.99  inst_num_of_non_proper_insts:           1020
% 3.65/0.99  inst_num_of_duplicates:                 0
% 3.65/0.99  inst_inst_num_from_inst_to_res:         0
% 3.65/0.99  inst_dismatching_checking_time:         0.
% 3.65/0.99  
% 3.65/0.99  ------ Resolution
% 3.65/0.99  
% 3.65/0.99  res_num_of_clauses:                     0
% 3.65/0.99  res_num_in_passive:                     0
% 3.65/0.99  res_num_in_active:                      0
% 3.65/0.99  res_num_of_loops:                       171
% 3.65/0.99  res_forward_subset_subsumed:            106
% 3.65/0.99  res_backward_subset_subsumed:           0
% 3.65/0.99  res_forward_subsumed:                   1
% 3.65/0.99  res_backward_subsumed:                  1
% 3.65/0.99  res_forward_subsumption_resolution:     1
% 3.65/0.99  res_backward_subsumption_resolution:    0
% 3.65/0.99  res_clause_to_clause_subsumption:       443
% 3.65/0.99  res_orphan_elimination:                 0
% 3.65/0.99  res_tautology_del:                      167
% 3.65/0.99  res_num_eq_res_simplified:              0
% 3.65/0.99  res_num_sel_changes:                    0
% 3.65/0.99  res_moves_from_active_to_pass:          0
% 3.65/0.99  
% 3.65/0.99  ------ Superposition
% 3.65/0.99  
% 3.65/0.99  sup_time_total:                         0.
% 3.65/0.99  sup_time_generating:                    0.
% 3.65/0.99  sup_time_sim_full:                      0.
% 3.65/0.99  sup_time_sim_immed:                     0.
% 3.65/0.99  
% 3.65/0.99  sup_num_of_clauses:                     172
% 3.65/0.99  sup_num_in_active:                      80
% 3.65/0.99  sup_num_in_passive:                     92
% 3.65/0.99  sup_num_of_loops:                       91
% 3.65/0.99  sup_fw_superposition:                   89
% 3.65/0.99  sup_bw_superposition:                   121
% 3.65/0.99  sup_immediate_simplified:               27
% 3.65/0.99  sup_given_eliminated:                   0
% 3.65/0.99  comparisons_done:                       0
% 3.65/0.99  comparisons_avoided:                    0
% 3.65/0.99  
% 3.65/0.99  ------ Simplifications
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  sim_fw_subset_subsumed:                 19
% 3.65/0.99  sim_bw_subset_subsumed:                 6
% 3.65/0.99  sim_fw_subsumed:                        6
% 3.65/0.99  sim_bw_subsumed:                        1
% 3.65/0.99  sim_fw_subsumption_res:                 4
% 3.65/0.99  sim_bw_subsumption_res:                 0
% 3.65/0.99  sim_tautology_del:                      16
% 3.65/0.99  sim_eq_tautology_del:                   2
% 3.65/0.99  sim_eq_res_simp:                        0
% 3.65/0.99  sim_fw_demodulated:                     0
% 3.65/0.99  sim_bw_demodulated:                     7
% 3.65/0.99  sim_light_normalised:                   1
% 3.65/0.99  sim_joinable_taut:                      0
% 3.65/0.99  sim_joinable_simp:                      0
% 3.65/0.99  sim_ac_normalised:                      0
% 3.65/0.99  sim_smt_subsumption:                    0
% 3.65/0.99  
%------------------------------------------------------------------------------
