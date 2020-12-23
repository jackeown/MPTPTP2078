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
% DateTime   : Thu Dec  3 12:26:54 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  234 (2436 expanded)
%              Number of clauses        :  146 ( 643 expanded)
%              Number of leaves         :   25 ( 539 expanded)
%              Depth                    :   25
%              Number of atoms          :  877 (16040 expanded)
%              Number of equality atoms :  243 ( 854 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK4)
          | ~ v2_tex_2(sK4,X0) )
        & ( v1_zfmisc_1(sK4)
          | v2_tex_2(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
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
            | ~ v2_tex_2(X1,sK3) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ( ~ v1_zfmisc_1(sK4)
      | ~ v2_tex_2(sK4,sK3) )
    & ( v1_zfmisc_1(sK4)
      | v2_tex_2(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & ~ v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f57,f59,f58])).

fof(f95,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f94,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f60])).

fof(f15,axiom,(
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

fof(f19,plain,(
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
    inference(pure_predicate_removal,[],[f15])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & v1_tdlat_3(sK2(X0,X1))
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & v1_tdlat_3(sK2(X0,X1))
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f54])).

fof(f87,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f90,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f92,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f93,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).

fof(f62,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f83,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f12,axiom,(
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

fof(f32,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f80,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f78,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f75,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f96,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2867,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_zfmisc_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_7437,plain,
    ( v1_zfmisc_1(X0)
    | ~ v1_zfmisc_1(u1_struct_0(sK2(X1,sK4)))
    | X0 != u1_struct_0(sK2(X1,sK4)) ),
    inference(instantiation,[status(thm)],[c_2867])).

cnf(c_12424,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK2(X0,sK4)))
    | v1_zfmisc_1(sK4)
    | sK4 != u1_struct_0(sK2(X0,sK4)) ),
    inference(instantiation,[status(thm)],[c_7437])).

cnf(c_12426,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | v1_zfmisc_1(sK4)
    | sK4 != u1_struct_0(sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_12424])).

cnf(c_29,negated_conjecture,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3681,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3680,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_23,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3687,plain,
    ( u1_struct_0(sK2(X0,X1)) = X1
    | v2_tex_2(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5902,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3680,c_3687])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_36,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_37,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_39,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_40,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6461,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5902,c_36,c_37,c_39,c_40])).

cnf(c_6467,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3681,c_6461])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3703,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_218,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_1])).

cnf(c_219,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_218])).

cnf(c_3674,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_4437,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3703,c_3674])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3690,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6095,plain,
    ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4437,c_3690])).

cnf(c_3679,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6839,plain,
    ( k6_domain_1(sK4,sK0(sK4)) = k1_tarski(sK0(sK4)) ),
    inference(superposition,[status(thm)],[c_6095,c_3679])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3691,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6925,plain,
    ( m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4)) = iProver_top
    | m1_subset_1(sK0(sK4),sK4) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6839,c_3691])).

cnf(c_3978,plain,
    ( r2_hidden(sK0(sK4),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3979,plain,
    ( r2_hidden(sK0(sK4),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3978])).

cnf(c_4178,plain,
    ( m1_subset_1(X0,sK4)
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_219])).

cnf(c_4419,plain,
    ( m1_subset_1(sK0(sK4),sK4)
    | ~ r2_hidden(sK0(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_4178])).

cnf(c_4420,plain,
    ( m1_subset_1(sK0(sK4),sK4) = iProver_top
    | r2_hidden(sK0(sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4419])).

cnf(c_7046,plain,
    ( m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6925,c_40,c_3979,c_4420])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3693,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7053,plain,
    ( r1_tarski(k1_tarski(sK0(sK4)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7046,c_3693])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3688,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7148,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v1_zfmisc_1(sK4) != iProver_top
    | v1_xboole_0(k1_tarski(sK0(sK4))) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7053,c_3688])).

cnf(c_8325,plain,
    ( v1_xboole_0(k1_tarski(sK0(sK4))) = iProver_top
    | v1_zfmisc_1(sK4) != iProver_top
    | k1_tarski(sK0(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7148,c_40])).

cnf(c_8326,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v1_zfmisc_1(sK4) != iProver_top
    | v1_xboole_0(k1_tarski(sK0(sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_8325])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3698,plain,
    ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8332,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v1_zfmisc_1(sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8326,c_3698])).

cnf(c_8334,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | k1_tarski(sK0(sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_6467,c_8332])).

cnf(c_19,plain,
    ( v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_17,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_202,plain,
    ( ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_17])).

cnf(c_203,plain,
    ( v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_202])).

cnf(c_12,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_14,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_465,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_12,c_14])).

cnf(c_483,plain,
    ( v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_203,c_465])).

cnf(c_3673,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v2_tdlat_3(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_8949,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | v2_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top
    | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8334,c_3673])).

cnf(c_42,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_282,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(prop_impl,[status(thm)],[c_29])).

cnf(c_283,plain,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(renaming,[status(thm)],[c_282])).

cnf(c_981,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_283])).

cnf(c_982,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(sK2(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_981])).

cnf(c_984,plain,
    ( ~ v2_struct_0(sK2(sK3,sK4))
    | v1_zfmisc_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_982,c_35,c_34,c_32,c_31,c_30])).

cnf(c_986,plain,
    ( v2_struct_0(sK2(sK3,sK4)) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_984])).

cnf(c_25,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_tdlat_3(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_995,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_tdlat_3(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_283])).

cnf(c_996,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | v1_tdlat_3(sK2(sK3,sK4))
    | ~ v2_pre_topc(sK3)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_995])).

cnf(c_998,plain,
    ( v1_tdlat_3(sK2(sK3,sK4))
    | v1_zfmisc_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_996,c_35,c_34,c_32,c_31,c_30])).

cnf(c_1000,plain,
    ( v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_998])).

cnf(c_24,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3686,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_pre_topc(sK2(X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6035,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3680,c_3686])).

cnf(c_6587,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6035,c_36,c_37,c_39,c_40])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3692,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6593,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | l1_pre_topc(sK2(sK3,sK4)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6587,c_3692])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1225,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X2)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_1226,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_1225])).

cnf(c_3672,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_tdlat_3(X1) != iProver_top
    | v2_tdlat_3(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1226])).

cnf(c_6594,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_tdlat_3(sK2(sK3,sK4)) = iProver_top
    | v2_tdlat_3(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6587,c_3672])).

cnf(c_33,negated_conjecture,
    ( v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_38,plain,
    ( v2_tdlat_3(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6697,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v2_tdlat_3(sK2(sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6594,c_36,c_38,c_39])).

cnf(c_9156,plain,
    ( k1_tarski(sK0(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8949,c_39,c_42,c_986,c_1000,c_6593,c_6697,c_8332])).

cnf(c_4352,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3680,c_3693])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3699,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5045,plain,
    ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4352,c_3699])).

cnf(c_5446,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5045,c_3674])).

cnf(c_5707,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
    | r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5446,c_3690])).

cnf(c_4127,plain,
    ( ~ r1_tarski(sK4,X0)
    | r2_hidden(sK0(sK4),X0)
    | ~ r2_hidden(sK0(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4677,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(X0))
    | r2_hidden(sK0(sK4),u1_struct_0(X0))
    | ~ r2_hidden(sK0(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_4127])).

cnf(c_4679,plain,
    ( r1_tarski(sK4,u1_struct_0(X0)) != iProver_top
    | r2_hidden(sK0(sK4),u1_struct_0(X0)) = iProver_top
    | r2_hidden(sK0(sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4677])).

cnf(c_4681,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(sK4),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(sK4),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4679])).

cnf(c_4664,plain,
    ( ~ r2_hidden(sK0(sK4),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5220,plain,
    ( ~ r2_hidden(sK0(sK4),u1_struct_0(X0))
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_4664])).

cnf(c_5221,plain,
    ( r2_hidden(sK0(sK4),u1_struct_0(X0)) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5220])).

cnf(c_5223,plain,
    ( r2_hidden(sK0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5221])).

cnf(c_8299,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5707,c_40,c_3979,c_4352,c_4681,c_5223])).

cnf(c_8300,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_8299])).

cnf(c_8307,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4))
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3703,c_8300])).

cnf(c_8560,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8307,c_40])).

cnf(c_9160,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = sK4 ),
    inference(demodulation,[status(thm)],[c_9156,c_8560])).

cnf(c_27,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3683,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10103,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9160,c_3683])).

cnf(c_10114,plain,
    ( v2_tex_2(sK4,sK3)
    | ~ m1_subset_1(sK0(sK4),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10103])).

cnf(c_6699,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v2_tdlat_3(sK2(sK3,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6697])).

cnf(c_6611,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | l1_pre_topc(sK2(sK3,sK4))
    | ~ l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6593])).

cnf(c_2859,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4162,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_2859])).

cnf(c_4423,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4162])).

cnf(c_6558,plain,
    ( u1_struct_0(sK2(X0,sK4)) != sK4
    | sK4 = u1_struct_0(sK2(X0,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4423])).

cnf(c_6564,plain,
    ( u1_struct_0(sK2(sK3,sK4)) != sK4
    | sK4 = u1_struct_0(sK2(sK3,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_6558])).

cnf(c_6547,plain,
    ( v2_struct_0(sK2(X0,sK4))
    | ~ v1_tdlat_3(sK2(X0,sK4))
    | ~ v2_tdlat_3(sK2(X0,sK4))
    | v1_zfmisc_1(u1_struct_0(sK2(X0,sK4)))
    | ~ l1_pre_topc(sK2(X0,sK4)) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_6549,plain,
    ( v2_struct_0(sK2(sK3,sK4))
    | ~ v1_tdlat_3(sK2(sK3,sK4))
    | ~ v2_tdlat_3(sK2(sK3,sK4))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | ~ l1_pre_topc(sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_6547])).

cnf(c_3684,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK2(X1,X0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5841,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v2_struct_0(sK2(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3680,c_3684])).

cnf(c_6530,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v2_struct_0(sK2(sK3,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5841,c_36,c_37,c_39,c_40])).

cnf(c_6532,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ v2_struct_0(sK2(sK3,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6530])).

cnf(c_3685,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_tdlat_3(sK2(X1,X0)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5255,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3680,c_3685])).

cnf(c_5378,plain,
    ( v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
    | v2_tex_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5255,c_36,c_37,c_39,c_40])).

cnf(c_5379,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5378])).

cnf(c_5380,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_tdlat_3(sK2(sK3,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5379])).

cnf(c_4058,plain,
    ( m1_subset_1(X0,u1_struct_0(X1))
    | ~ r2_hidden(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_219])).

cnf(c_4678,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(X0))
    | ~ r2_hidden(sK0(sK4),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_4058])).

cnf(c_4683,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
    | r2_hidden(sK0(sK4),u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4678])).

cnf(c_4685,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4683])).

cnf(c_4684,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(sK4),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4678])).

cnf(c_4680,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | r2_hidden(sK0(sK4),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_4677])).

cnf(c_2858,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4424,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2858])).

cnf(c_4353,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4352])).

cnf(c_28,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12426,c_10114,c_10103,c_6699,c_6611,c_6564,c_6549,c_6532,c_6461,c_5380,c_4685,c_4684,c_4681,c_4680,c_4424,c_4353,c_4352,c_3979,c_3978,c_28,c_40,c_31,c_39,c_32,c_37,c_34,c_36,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:17:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.28/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.00  
% 3.28/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.28/1.00  
% 3.28/1.00  ------  iProver source info
% 3.28/1.00  
% 3.28/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.28/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.28/1.00  git: non_committed_changes: false
% 3.28/1.00  git: last_make_outside_of_git: false
% 3.28/1.00  
% 3.28/1.00  ------ 
% 3.28/1.00  
% 3.28/1.00  ------ Input Options
% 3.28/1.00  
% 3.28/1.00  --out_options                           all
% 3.28/1.00  --tptp_safe_out                         true
% 3.28/1.00  --problem_path                          ""
% 3.28/1.00  --include_path                          ""
% 3.28/1.00  --clausifier                            res/vclausify_rel
% 3.28/1.00  --clausifier_options                    --mode clausify
% 3.28/1.00  --stdin                                 false
% 3.28/1.00  --stats_out                             all
% 3.28/1.00  
% 3.28/1.00  ------ General Options
% 3.28/1.00  
% 3.28/1.00  --fof                                   false
% 3.28/1.00  --time_out_real                         305.
% 3.28/1.00  --time_out_virtual                      -1.
% 3.28/1.00  --symbol_type_check                     false
% 3.28/1.00  --clausify_out                          false
% 3.28/1.00  --sig_cnt_out                           false
% 3.28/1.00  --trig_cnt_out                          false
% 3.28/1.00  --trig_cnt_out_tolerance                1.
% 3.28/1.00  --trig_cnt_out_sk_spl                   false
% 3.28/1.00  --abstr_cl_out                          false
% 3.28/1.00  
% 3.28/1.00  ------ Global Options
% 3.28/1.00  
% 3.28/1.00  --schedule                              default
% 3.28/1.00  --add_important_lit                     false
% 3.28/1.00  --prop_solver_per_cl                    1000
% 3.28/1.00  --min_unsat_core                        false
% 3.28/1.00  --soft_assumptions                      false
% 3.28/1.00  --soft_lemma_size                       3
% 3.28/1.00  --prop_impl_unit_size                   0
% 3.28/1.00  --prop_impl_unit                        []
% 3.28/1.00  --share_sel_clauses                     true
% 3.28/1.00  --reset_solvers                         false
% 3.28/1.00  --bc_imp_inh                            [conj_cone]
% 3.28/1.00  --conj_cone_tolerance                   3.
% 3.28/1.00  --extra_neg_conj                        none
% 3.28/1.00  --large_theory_mode                     true
% 3.28/1.00  --prolific_symb_bound                   200
% 3.28/1.00  --lt_threshold                          2000
% 3.28/1.00  --clause_weak_htbl                      true
% 3.28/1.00  --gc_record_bc_elim                     false
% 3.28/1.00  
% 3.28/1.00  ------ Preprocessing Options
% 3.28/1.00  
% 3.28/1.00  --preprocessing_flag                    true
% 3.28/1.00  --time_out_prep_mult                    0.1
% 3.28/1.00  --splitting_mode                        input
% 3.28/1.00  --splitting_grd                         true
% 3.28/1.00  --splitting_cvd                         false
% 3.28/1.00  --splitting_cvd_svl                     false
% 3.28/1.00  --splitting_nvd                         32
% 3.28/1.00  --sub_typing                            true
% 3.28/1.00  --prep_gs_sim                           true
% 3.28/1.00  --prep_unflatten                        true
% 3.28/1.00  --prep_res_sim                          true
% 3.28/1.00  --prep_upred                            true
% 3.28/1.00  --prep_sem_filter                       exhaustive
% 3.28/1.00  --prep_sem_filter_out                   false
% 3.28/1.00  --pred_elim                             true
% 3.28/1.00  --res_sim_input                         true
% 3.28/1.00  --eq_ax_congr_red                       true
% 3.28/1.00  --pure_diseq_elim                       true
% 3.28/1.00  --brand_transform                       false
% 3.28/1.00  --non_eq_to_eq                          false
% 3.28/1.00  --prep_def_merge                        true
% 3.28/1.00  --prep_def_merge_prop_impl              false
% 3.28/1.00  --prep_def_merge_mbd                    true
% 3.28/1.00  --prep_def_merge_tr_red                 false
% 3.28/1.00  --prep_def_merge_tr_cl                  false
% 3.28/1.00  --smt_preprocessing                     true
% 3.28/1.00  --smt_ac_axioms                         fast
% 3.28/1.00  --preprocessed_out                      false
% 3.28/1.00  --preprocessed_stats                    false
% 3.28/1.00  
% 3.28/1.00  ------ Abstraction refinement Options
% 3.28/1.00  
% 3.28/1.00  --abstr_ref                             []
% 3.28/1.00  --abstr_ref_prep                        false
% 3.28/1.00  --abstr_ref_until_sat                   false
% 3.28/1.00  --abstr_ref_sig_restrict                funpre
% 3.28/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.28/1.00  --abstr_ref_under                       []
% 3.28/1.00  
% 3.28/1.00  ------ SAT Options
% 3.28/1.00  
% 3.28/1.00  --sat_mode                              false
% 3.28/1.00  --sat_fm_restart_options                ""
% 3.28/1.00  --sat_gr_def                            false
% 3.28/1.00  --sat_epr_types                         true
% 3.28/1.00  --sat_non_cyclic_types                  false
% 3.28/1.00  --sat_finite_models                     false
% 3.28/1.00  --sat_fm_lemmas                         false
% 3.28/1.00  --sat_fm_prep                           false
% 3.28/1.00  --sat_fm_uc_incr                        true
% 3.28/1.00  --sat_out_model                         small
% 3.28/1.00  --sat_out_clauses                       false
% 3.28/1.00  
% 3.28/1.00  ------ QBF Options
% 3.28/1.00  
% 3.28/1.00  --qbf_mode                              false
% 3.28/1.00  --qbf_elim_univ                         false
% 3.28/1.00  --qbf_dom_inst                          none
% 3.28/1.00  --qbf_dom_pre_inst                      false
% 3.28/1.00  --qbf_sk_in                             false
% 3.28/1.00  --qbf_pred_elim                         true
% 3.28/1.00  --qbf_split                             512
% 3.28/1.00  
% 3.28/1.00  ------ BMC1 Options
% 3.28/1.00  
% 3.28/1.00  --bmc1_incremental                      false
% 3.28/1.00  --bmc1_axioms                           reachable_all
% 3.28/1.00  --bmc1_min_bound                        0
% 3.28/1.00  --bmc1_max_bound                        -1
% 3.28/1.00  --bmc1_max_bound_default                -1
% 3.28/1.00  --bmc1_symbol_reachability              true
% 3.28/1.00  --bmc1_property_lemmas                  false
% 3.28/1.00  --bmc1_k_induction                      false
% 3.28/1.00  --bmc1_non_equiv_states                 false
% 3.28/1.00  --bmc1_deadlock                         false
% 3.28/1.00  --bmc1_ucm                              false
% 3.28/1.00  --bmc1_add_unsat_core                   none
% 3.28/1.00  --bmc1_unsat_core_children              false
% 3.28/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.28/1.00  --bmc1_out_stat                         full
% 3.28/1.00  --bmc1_ground_init                      false
% 3.28/1.00  --bmc1_pre_inst_next_state              false
% 3.28/1.00  --bmc1_pre_inst_state                   false
% 3.28/1.00  --bmc1_pre_inst_reach_state             false
% 3.28/1.00  --bmc1_out_unsat_core                   false
% 3.28/1.00  --bmc1_aig_witness_out                  false
% 3.28/1.00  --bmc1_verbose                          false
% 3.28/1.00  --bmc1_dump_clauses_tptp                false
% 3.28/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.28/1.00  --bmc1_dump_file                        -
% 3.28/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.28/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.28/1.00  --bmc1_ucm_extend_mode                  1
% 3.28/1.00  --bmc1_ucm_init_mode                    2
% 3.28/1.00  --bmc1_ucm_cone_mode                    none
% 3.28/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.28/1.00  --bmc1_ucm_relax_model                  4
% 3.28/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.28/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.28/1.00  --bmc1_ucm_layered_model                none
% 3.28/1.00  --bmc1_ucm_max_lemma_size               10
% 3.28/1.00  
% 3.28/1.00  ------ AIG Options
% 3.28/1.00  
% 3.28/1.00  --aig_mode                              false
% 3.28/1.00  
% 3.28/1.00  ------ Instantiation Options
% 3.28/1.00  
% 3.28/1.00  --instantiation_flag                    true
% 3.28/1.00  --inst_sos_flag                         false
% 3.28/1.00  --inst_sos_phase                        true
% 3.28/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.28/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.28/1.00  --inst_lit_sel_side                     num_symb
% 3.28/1.00  --inst_solver_per_active                1400
% 3.28/1.00  --inst_solver_calls_frac                1.
% 3.28/1.00  --inst_passive_queue_type               priority_queues
% 3.28/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.28/1.00  --inst_passive_queues_freq              [25;2]
% 3.28/1.00  --inst_dismatching                      true
% 3.28/1.00  --inst_eager_unprocessed_to_passive     true
% 3.28/1.00  --inst_prop_sim_given                   true
% 3.28/1.00  --inst_prop_sim_new                     false
% 3.28/1.00  --inst_subs_new                         false
% 3.28/1.00  --inst_eq_res_simp                      false
% 3.28/1.00  --inst_subs_given                       false
% 3.28/1.00  --inst_orphan_elimination               true
% 3.28/1.00  --inst_learning_loop_flag               true
% 3.28/1.00  --inst_learning_start                   3000
% 3.28/1.00  --inst_learning_factor                  2
% 3.28/1.00  --inst_start_prop_sim_after_learn       3
% 3.28/1.00  --inst_sel_renew                        solver
% 3.28/1.00  --inst_lit_activity_flag                true
% 3.28/1.00  --inst_restr_to_given                   false
% 3.28/1.00  --inst_activity_threshold               500
% 3.28/1.00  --inst_out_proof                        true
% 3.28/1.00  
% 3.28/1.00  ------ Resolution Options
% 3.28/1.00  
% 3.28/1.00  --resolution_flag                       true
% 3.28/1.00  --res_lit_sel                           adaptive
% 3.28/1.00  --res_lit_sel_side                      none
% 3.28/1.00  --res_ordering                          kbo
% 3.28/1.00  --res_to_prop_solver                    active
% 3.28/1.00  --res_prop_simpl_new                    false
% 3.28/1.00  --res_prop_simpl_given                  true
% 3.28/1.00  --res_passive_queue_type                priority_queues
% 3.28/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.28/1.00  --res_passive_queues_freq               [15;5]
% 3.28/1.00  --res_forward_subs                      full
% 3.28/1.00  --res_backward_subs                     full
% 3.28/1.00  --res_forward_subs_resolution           true
% 3.28/1.00  --res_backward_subs_resolution          true
% 3.28/1.00  --res_orphan_elimination                true
% 3.28/1.00  --res_time_limit                        2.
% 3.28/1.00  --res_out_proof                         true
% 3.28/1.00  
% 3.28/1.00  ------ Superposition Options
% 3.28/1.00  
% 3.28/1.00  --superposition_flag                    true
% 3.28/1.00  --sup_passive_queue_type                priority_queues
% 3.28/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.28/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.28/1.00  --demod_completeness_check              fast
% 3.28/1.00  --demod_use_ground                      true
% 3.28/1.00  --sup_to_prop_solver                    passive
% 3.28/1.00  --sup_prop_simpl_new                    true
% 3.28/1.00  --sup_prop_simpl_given                  true
% 3.28/1.00  --sup_fun_splitting                     false
% 3.28/1.00  --sup_smt_interval                      50000
% 3.28/1.00  
% 3.28/1.00  ------ Superposition Simplification Setup
% 3.28/1.00  
% 3.28/1.00  --sup_indices_passive                   []
% 3.28/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.28/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.00  --sup_full_bw                           [BwDemod]
% 3.28/1.00  --sup_immed_triv                        [TrivRules]
% 3.28/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.28/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.00  --sup_immed_bw_main                     []
% 3.28/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.28/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/1.00  
% 3.28/1.00  ------ Combination Options
% 3.28/1.00  
% 3.28/1.00  --comb_res_mult                         3
% 3.28/1.00  --comb_sup_mult                         2
% 3.28/1.00  --comb_inst_mult                        10
% 3.28/1.00  
% 3.28/1.00  ------ Debug Options
% 3.28/1.00  
% 3.28/1.00  --dbg_backtrace                         false
% 3.28/1.00  --dbg_dump_prop_clauses                 false
% 3.28/1.00  --dbg_dump_prop_clauses_file            -
% 3.28/1.00  --dbg_out_stat                          false
% 3.28/1.00  ------ Parsing...
% 3.28/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.28/1.00  
% 3.28/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.28/1.00  
% 3.28/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.28/1.00  
% 3.28/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.28/1.00  ------ Proving...
% 3.28/1.00  ------ Problem Properties 
% 3.28/1.00  
% 3.28/1.00  
% 3.28/1.00  clauses                                 32
% 3.28/1.00  conjectures                             8
% 3.28/1.00  EPR                                     17
% 3.28/1.00  Horn                                    18
% 3.28/1.00  unary                                   7
% 3.28/1.00  binary                                  9
% 3.28/1.00  lits                                    97
% 3.28/1.00  lits eq                                 3
% 3.28/1.00  fd_pure                                 0
% 3.28/1.00  fd_pseudo                               0
% 3.28/1.00  fd_cond                                 0
% 3.28/1.00  fd_pseudo_cond                          1
% 3.28/1.00  AC symbols                              0
% 3.28/1.00  
% 3.28/1.00  ------ Schedule dynamic 5 is on 
% 3.28/1.00  
% 3.28/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.28/1.00  
% 3.28/1.00  
% 3.28/1.00  ------ 
% 3.28/1.00  Current options:
% 3.28/1.00  ------ 
% 3.28/1.00  
% 3.28/1.00  ------ Input Options
% 3.28/1.00  
% 3.28/1.00  --out_options                           all
% 3.28/1.00  --tptp_safe_out                         true
% 3.28/1.00  --problem_path                          ""
% 3.28/1.00  --include_path                          ""
% 3.28/1.00  --clausifier                            res/vclausify_rel
% 3.28/1.00  --clausifier_options                    --mode clausify
% 3.28/1.00  --stdin                                 false
% 3.28/1.00  --stats_out                             all
% 3.28/1.00  
% 3.28/1.00  ------ General Options
% 3.28/1.00  
% 3.28/1.00  --fof                                   false
% 3.28/1.00  --time_out_real                         305.
% 3.28/1.00  --time_out_virtual                      -1.
% 3.28/1.00  --symbol_type_check                     false
% 3.28/1.00  --clausify_out                          false
% 3.28/1.00  --sig_cnt_out                           false
% 3.28/1.00  --trig_cnt_out                          false
% 3.28/1.00  --trig_cnt_out_tolerance                1.
% 3.28/1.00  --trig_cnt_out_sk_spl                   false
% 3.28/1.00  --abstr_cl_out                          false
% 3.28/1.00  
% 3.28/1.00  ------ Global Options
% 3.28/1.00  
% 3.28/1.00  --schedule                              default
% 3.28/1.00  --add_important_lit                     false
% 3.28/1.00  --prop_solver_per_cl                    1000
% 3.28/1.00  --min_unsat_core                        false
% 3.28/1.00  --soft_assumptions                      false
% 3.28/1.00  --soft_lemma_size                       3
% 3.28/1.00  --prop_impl_unit_size                   0
% 3.28/1.00  --prop_impl_unit                        []
% 3.28/1.00  --share_sel_clauses                     true
% 3.28/1.00  --reset_solvers                         false
% 3.28/1.00  --bc_imp_inh                            [conj_cone]
% 3.28/1.00  --conj_cone_tolerance                   3.
% 3.28/1.00  --extra_neg_conj                        none
% 3.28/1.00  --large_theory_mode                     true
% 3.28/1.00  --prolific_symb_bound                   200
% 3.28/1.00  --lt_threshold                          2000
% 3.28/1.00  --clause_weak_htbl                      true
% 3.28/1.00  --gc_record_bc_elim                     false
% 3.28/1.00  
% 3.28/1.00  ------ Preprocessing Options
% 3.28/1.00  
% 3.28/1.00  --preprocessing_flag                    true
% 3.28/1.00  --time_out_prep_mult                    0.1
% 3.28/1.00  --splitting_mode                        input
% 3.28/1.00  --splitting_grd                         true
% 3.28/1.00  --splitting_cvd                         false
% 3.28/1.00  --splitting_cvd_svl                     false
% 3.28/1.00  --splitting_nvd                         32
% 3.28/1.00  --sub_typing                            true
% 3.28/1.00  --prep_gs_sim                           true
% 3.28/1.00  --prep_unflatten                        true
% 3.28/1.00  --prep_res_sim                          true
% 3.28/1.00  --prep_upred                            true
% 3.28/1.00  --prep_sem_filter                       exhaustive
% 3.28/1.00  --prep_sem_filter_out                   false
% 3.28/1.00  --pred_elim                             true
% 3.28/1.00  --res_sim_input                         true
% 3.28/1.00  --eq_ax_congr_red                       true
% 3.28/1.00  --pure_diseq_elim                       true
% 3.28/1.00  --brand_transform                       false
% 3.28/1.00  --non_eq_to_eq                          false
% 3.28/1.00  --prep_def_merge                        true
% 3.28/1.00  --prep_def_merge_prop_impl              false
% 3.28/1.00  --prep_def_merge_mbd                    true
% 3.28/1.00  --prep_def_merge_tr_red                 false
% 3.28/1.00  --prep_def_merge_tr_cl                  false
% 3.28/1.00  --smt_preprocessing                     true
% 3.28/1.00  --smt_ac_axioms                         fast
% 3.28/1.00  --preprocessed_out                      false
% 3.28/1.00  --preprocessed_stats                    false
% 3.28/1.00  
% 3.28/1.00  ------ Abstraction refinement Options
% 3.28/1.00  
% 3.28/1.00  --abstr_ref                             []
% 3.28/1.00  --abstr_ref_prep                        false
% 3.28/1.00  --abstr_ref_until_sat                   false
% 3.28/1.00  --abstr_ref_sig_restrict                funpre
% 3.28/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.28/1.00  --abstr_ref_under                       []
% 3.28/1.00  
% 3.28/1.00  ------ SAT Options
% 3.28/1.00  
% 3.28/1.00  --sat_mode                              false
% 3.28/1.00  --sat_fm_restart_options                ""
% 3.28/1.00  --sat_gr_def                            false
% 3.28/1.00  --sat_epr_types                         true
% 3.28/1.00  --sat_non_cyclic_types                  false
% 3.28/1.00  --sat_finite_models                     false
% 3.28/1.00  --sat_fm_lemmas                         false
% 3.28/1.00  --sat_fm_prep                           false
% 3.28/1.00  --sat_fm_uc_incr                        true
% 3.28/1.00  --sat_out_model                         small
% 3.28/1.00  --sat_out_clauses                       false
% 3.28/1.00  
% 3.28/1.00  ------ QBF Options
% 3.28/1.00  
% 3.28/1.00  --qbf_mode                              false
% 3.28/1.00  --qbf_elim_univ                         false
% 3.28/1.00  --qbf_dom_inst                          none
% 3.28/1.00  --qbf_dom_pre_inst                      false
% 3.28/1.00  --qbf_sk_in                             false
% 3.28/1.00  --qbf_pred_elim                         true
% 3.28/1.00  --qbf_split                             512
% 3.28/1.00  
% 3.28/1.00  ------ BMC1 Options
% 3.28/1.00  
% 3.28/1.00  --bmc1_incremental                      false
% 3.28/1.00  --bmc1_axioms                           reachable_all
% 3.28/1.00  --bmc1_min_bound                        0
% 3.28/1.00  --bmc1_max_bound                        -1
% 3.28/1.00  --bmc1_max_bound_default                -1
% 3.28/1.00  --bmc1_symbol_reachability              true
% 3.28/1.00  --bmc1_property_lemmas                  false
% 3.28/1.00  --bmc1_k_induction                      false
% 3.28/1.00  --bmc1_non_equiv_states                 false
% 3.28/1.00  --bmc1_deadlock                         false
% 3.28/1.00  --bmc1_ucm                              false
% 3.28/1.00  --bmc1_add_unsat_core                   none
% 3.28/1.00  --bmc1_unsat_core_children              false
% 3.28/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.28/1.00  --bmc1_out_stat                         full
% 3.28/1.00  --bmc1_ground_init                      false
% 3.28/1.00  --bmc1_pre_inst_next_state              false
% 3.28/1.00  --bmc1_pre_inst_state                   false
% 3.28/1.00  --bmc1_pre_inst_reach_state             false
% 3.28/1.00  --bmc1_out_unsat_core                   false
% 3.28/1.00  --bmc1_aig_witness_out                  false
% 3.28/1.00  --bmc1_verbose                          false
% 3.28/1.00  --bmc1_dump_clauses_tptp                false
% 3.28/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.28/1.00  --bmc1_dump_file                        -
% 3.28/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.28/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.28/1.00  --bmc1_ucm_extend_mode                  1
% 3.28/1.00  --bmc1_ucm_init_mode                    2
% 3.28/1.00  --bmc1_ucm_cone_mode                    none
% 3.28/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.28/1.00  --bmc1_ucm_relax_model                  4
% 3.28/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.28/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.28/1.00  --bmc1_ucm_layered_model                none
% 3.28/1.00  --bmc1_ucm_max_lemma_size               10
% 3.28/1.00  
% 3.28/1.00  ------ AIG Options
% 3.28/1.00  
% 3.28/1.00  --aig_mode                              false
% 3.28/1.00  
% 3.28/1.00  ------ Instantiation Options
% 3.28/1.00  
% 3.28/1.00  --instantiation_flag                    true
% 3.28/1.00  --inst_sos_flag                         false
% 3.28/1.00  --inst_sos_phase                        true
% 3.28/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.28/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.28/1.00  --inst_lit_sel_side                     none
% 3.28/1.00  --inst_solver_per_active                1400
% 3.28/1.00  --inst_solver_calls_frac                1.
% 3.28/1.00  --inst_passive_queue_type               priority_queues
% 3.28/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.28/1.00  --inst_passive_queues_freq              [25;2]
% 3.28/1.00  --inst_dismatching                      true
% 3.28/1.00  --inst_eager_unprocessed_to_passive     true
% 3.28/1.00  --inst_prop_sim_given                   true
% 3.28/1.00  --inst_prop_sim_new                     false
% 3.28/1.00  --inst_subs_new                         false
% 3.28/1.00  --inst_eq_res_simp                      false
% 3.28/1.00  --inst_subs_given                       false
% 3.28/1.00  --inst_orphan_elimination               true
% 3.28/1.00  --inst_learning_loop_flag               true
% 3.28/1.00  --inst_learning_start                   3000
% 3.28/1.00  --inst_learning_factor                  2
% 3.28/1.00  --inst_start_prop_sim_after_learn       3
% 3.28/1.00  --inst_sel_renew                        solver
% 3.28/1.00  --inst_lit_activity_flag                true
% 3.28/1.00  --inst_restr_to_given                   false
% 3.28/1.00  --inst_activity_threshold               500
% 3.28/1.00  --inst_out_proof                        true
% 3.28/1.00  
% 3.28/1.00  ------ Resolution Options
% 3.28/1.00  
% 3.28/1.00  --resolution_flag                       false
% 3.28/1.00  --res_lit_sel                           adaptive
% 3.28/1.00  --res_lit_sel_side                      none
% 3.28/1.00  --res_ordering                          kbo
% 3.28/1.00  --res_to_prop_solver                    active
% 3.28/1.00  --res_prop_simpl_new                    false
% 3.28/1.00  --res_prop_simpl_given                  true
% 3.28/1.00  --res_passive_queue_type                priority_queues
% 3.28/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.28/1.00  --res_passive_queues_freq               [15;5]
% 3.28/1.00  --res_forward_subs                      full
% 3.28/1.00  --res_backward_subs                     full
% 3.28/1.00  --res_forward_subs_resolution           true
% 3.28/1.00  --res_backward_subs_resolution          true
% 3.28/1.00  --res_orphan_elimination                true
% 3.28/1.00  --res_time_limit                        2.
% 3.28/1.00  --res_out_proof                         true
% 3.28/1.00  
% 3.28/1.00  ------ Superposition Options
% 3.28/1.00  
% 3.28/1.00  --superposition_flag                    true
% 3.28/1.00  --sup_passive_queue_type                priority_queues
% 3.28/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.28/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.28/1.00  --demod_completeness_check              fast
% 3.28/1.00  --demod_use_ground                      true
% 3.28/1.00  --sup_to_prop_solver                    passive
% 3.28/1.00  --sup_prop_simpl_new                    true
% 3.28/1.00  --sup_prop_simpl_given                  true
% 3.28/1.00  --sup_fun_splitting                     false
% 3.28/1.00  --sup_smt_interval                      50000
% 3.28/1.00  
% 3.28/1.00  ------ Superposition Simplification Setup
% 3.28/1.00  
% 3.28/1.00  --sup_indices_passive                   []
% 3.28/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.28/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.00  --sup_full_bw                           [BwDemod]
% 3.28/1.00  --sup_immed_triv                        [TrivRules]
% 3.28/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.28/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.00  --sup_immed_bw_main                     []
% 3.28/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.28/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/1.00  
% 3.28/1.00  ------ Combination Options
% 3.28/1.00  
% 3.28/1.00  --comb_res_mult                         3
% 3.28/1.00  --comb_sup_mult                         2
% 3.28/1.00  --comb_inst_mult                        10
% 3.28/1.00  
% 3.28/1.00  ------ Debug Options
% 3.28/1.00  
% 3.28/1.00  --dbg_backtrace                         false
% 3.28/1.00  --dbg_dump_prop_clauses                 false
% 3.28/1.00  --dbg_dump_prop_clauses_file            -
% 3.28/1.00  --dbg_out_stat                          false
% 3.28/1.00  
% 3.28/1.00  
% 3.28/1.00  
% 3.28/1.00  
% 3.28/1.00  ------ Proving...
% 3.28/1.00  
% 3.28/1.00  
% 3.28/1.00  % SZS status Theorem for theBenchmark.p
% 3.28/1.00  
% 3.28/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.28/1.00  
% 3.28/1.00  fof(f17,conjecture,(
% 3.28/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.28/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f18,negated_conjecture,(
% 3.28/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.28/1.00    inference(negated_conjecture,[],[f17])).
% 3.28/1.00  
% 3.28/1.00  fof(f42,plain,(
% 3.28/1.00    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.28/1.00    inference(ennf_transformation,[],[f18])).
% 3.28/1.00  
% 3.28/1.00  fof(f43,plain,(
% 3.28/1.00    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.28/1.00    inference(flattening,[],[f42])).
% 3.28/1.00  
% 3.28/1.00  fof(f56,plain,(
% 3.28/1.00    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.28/1.00    inference(nnf_transformation,[],[f43])).
% 3.28/1.00  
% 3.28/1.00  fof(f57,plain,(
% 3.28/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.28/1.00    inference(flattening,[],[f56])).
% 3.28/1.00  
% 3.28/1.00  fof(f59,plain,(
% 3.28/1.00    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,X0)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK4))) )),
% 3.28/1.00    introduced(choice_axiom,[])).
% 3.28/1.00  
% 3.28/1.00  fof(f58,plain,(
% 3.28/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.28/1.00    introduced(choice_axiom,[])).
% 3.28/1.00  
% 3.28/1.00  fof(f60,plain,(
% 3.28/1.00    ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.28/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f57,f59,f58])).
% 3.28/1.00  
% 3.28/1.00  fof(f95,plain,(
% 3.28/1.00    v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)),
% 3.28/1.00    inference(cnf_transformation,[],[f60])).
% 3.28/1.00  
% 3.28/1.00  fof(f94,plain,(
% 3.28/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.28/1.00    inference(cnf_transformation,[],[f60])).
% 3.28/1.00  
% 3.28/1.00  fof(f15,axiom,(
% 3.28/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.28/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f19,plain,(
% 3.28/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.28/1.00    inference(pure_predicate_removal,[],[f15])).
% 3.28/1.00  
% 3.28/1.00  fof(f38,plain,(
% 3.28/1.00    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.28/1.00    inference(ennf_transformation,[],[f19])).
% 3.28/1.00  
% 3.28/1.00  fof(f39,plain,(
% 3.28/1.00    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.28/1.00    inference(flattening,[],[f38])).
% 3.28/1.00  
% 3.28/1.00  fof(f54,plain,(
% 3.28/1.00    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 3.28/1.00    introduced(choice_axiom,[])).
% 3.28/1.00  
% 3.28/1.00  fof(f55,plain,(
% 3.28/1.00    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.28/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f54])).
% 3.28/1.00  
% 3.28/1.00  fof(f87,plain,(
% 3.28/1.00    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f55])).
% 3.28/1.00  
% 3.28/1.00  fof(f89,plain,(
% 3.28/1.00    ~v2_struct_0(sK3)),
% 3.28/1.00    inference(cnf_transformation,[],[f60])).
% 3.28/1.00  
% 3.28/1.00  fof(f90,plain,(
% 3.28/1.00    v2_pre_topc(sK3)),
% 3.28/1.00    inference(cnf_transformation,[],[f60])).
% 3.28/1.00  
% 3.28/1.00  fof(f92,plain,(
% 3.28/1.00    l1_pre_topc(sK3)),
% 3.28/1.00    inference(cnf_transformation,[],[f60])).
% 3.28/1.00  
% 3.28/1.00  fof(f93,plain,(
% 3.28/1.00    ~v1_xboole_0(sK4)),
% 3.28/1.00    inference(cnf_transformation,[],[f60])).
% 3.28/1.00  
% 3.28/1.00  fof(f1,axiom,(
% 3.28/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.28/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f44,plain,(
% 3.28/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.28/1.00    inference(nnf_transformation,[],[f1])).
% 3.28/1.00  
% 3.28/1.00  fof(f45,plain,(
% 3.28/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.28/1.00    inference(rectify,[],[f44])).
% 3.28/1.00  
% 3.28/1.00  fof(f46,plain,(
% 3.28/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.28/1.00    introduced(choice_axiom,[])).
% 3.28/1.00  
% 3.28/1.00  fof(f47,plain,(
% 3.28/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.28/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).
% 3.28/1.00  
% 3.28/1.00  fof(f62,plain,(
% 3.28/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f47])).
% 3.28/1.00  
% 3.28/1.00  fof(f4,axiom,(
% 3.28/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.28/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f21,plain,(
% 3.28/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.28/1.00    inference(ennf_transformation,[],[f4])).
% 3.28/1.00  
% 3.28/1.00  fof(f52,plain,(
% 3.28/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.28/1.00    inference(nnf_transformation,[],[f21])).
% 3.28/1.00  
% 3.28/1.00  fof(f68,plain,(
% 3.28/1.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f52])).
% 3.28/1.00  
% 3.28/1.00  fof(f61,plain,(
% 3.28/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f47])).
% 3.28/1.00  
% 3.28/1.00  fof(f10,axiom,(
% 3.28/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.28/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f28,plain,(
% 3.28/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.28/1.00    inference(ennf_transformation,[],[f10])).
% 3.28/1.00  
% 3.28/1.00  fof(f29,plain,(
% 3.28/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.28/1.00    inference(flattening,[],[f28])).
% 3.28/1.00  
% 3.28/1.00  fof(f77,plain,(
% 3.28/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f29])).
% 3.28/1.00  
% 3.28/1.00  fof(f9,axiom,(
% 3.28/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.28/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f26,plain,(
% 3.28/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.28/1.00    inference(ennf_transformation,[],[f9])).
% 3.28/1.00  
% 3.28/1.00  fof(f27,plain,(
% 3.28/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.28/1.00    inference(flattening,[],[f26])).
% 3.28/1.00  
% 3.28/1.00  fof(f76,plain,(
% 3.28/1.00    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f27])).
% 3.28/1.00  
% 3.28/1.00  fof(f5,axiom,(
% 3.28/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.28/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f53,plain,(
% 3.28/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.28/1.00    inference(nnf_transformation,[],[f5])).
% 3.28/1.00  
% 3.28/1.00  fof(f71,plain,(
% 3.28/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.28/1.00    inference(cnf_transformation,[],[f53])).
% 3.28/1.00  
% 3.28/1.00  fof(f14,axiom,(
% 3.28/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.28/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f36,plain,(
% 3.28/1.00    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 3.28/1.00    inference(ennf_transformation,[],[f14])).
% 3.28/1.00  
% 3.28/1.00  fof(f37,plain,(
% 3.28/1.00    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.28/1.00    inference(flattening,[],[f36])).
% 3.28/1.00  
% 3.28/1.00  fof(f83,plain,(
% 3.28/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f37])).
% 3.28/1.00  
% 3.28/1.00  fof(f3,axiom,(
% 3.28/1.00    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.28/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f66,plain,(
% 3.28/1.00    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.28/1.00    inference(cnf_transformation,[],[f3])).
% 3.28/1.00  
% 3.28/1.00  fof(f12,axiom,(
% 3.28/1.00    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 3.28/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f32,plain,(
% 3.28/1.00    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.28/1.00    inference(ennf_transformation,[],[f12])).
% 3.28/1.00  
% 3.28/1.00  fof(f33,plain,(
% 3.28/1.00    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.28/1.00    inference(flattening,[],[f32])).
% 3.28/1.00  
% 3.28/1.00  fof(f80,plain,(
% 3.28/1.00    ( ! [X0] : (v7_struct_0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f33])).
% 3.28/1.00  
% 3.28/1.00  fof(f11,axiom,(
% 3.28/1.00    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.28/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f30,plain,(
% 3.28/1.00    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.28/1.00    inference(ennf_transformation,[],[f11])).
% 3.28/1.00  
% 3.28/1.00  fof(f31,plain,(
% 3.28/1.00    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.28/1.00    inference(flattening,[],[f30])).
% 3.28/1.00  
% 3.28/1.00  fof(f78,plain,(
% 3.28/1.00    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f31])).
% 3.28/1.00  
% 3.28/1.00  fof(f6,axiom,(
% 3.28/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.28/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f22,plain,(
% 3.28/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.28/1.00    inference(ennf_transformation,[],[f6])).
% 3.28/1.00  
% 3.28/1.00  fof(f73,plain,(
% 3.28/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f22])).
% 3.28/1.00  
% 3.28/1.00  fof(f8,axiom,(
% 3.28/1.00    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 3.28/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f24,plain,(
% 3.28/1.00    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 3.28/1.00    inference(ennf_transformation,[],[f8])).
% 3.28/1.00  
% 3.28/1.00  fof(f25,plain,(
% 3.28/1.00    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 3.28/1.00    inference(flattening,[],[f24])).
% 3.28/1.00  
% 3.28/1.00  fof(f75,plain,(
% 3.28/1.00    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f25])).
% 3.28/1.00  
% 3.28/1.00  fof(f84,plain,(
% 3.28/1.00    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f55])).
% 3.28/1.00  
% 3.28/1.00  fof(f85,plain,(
% 3.28/1.00    ( ! [X0,X1] : (v1_tdlat_3(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f55])).
% 3.28/1.00  
% 3.28/1.00  fof(f86,plain,(
% 3.28/1.00    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f55])).
% 3.28/1.00  
% 3.28/1.00  fof(f7,axiom,(
% 3.28/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.28/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f23,plain,(
% 3.28/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.28/1.00    inference(ennf_transformation,[],[f7])).
% 3.28/1.00  
% 3.28/1.00  fof(f74,plain,(
% 3.28/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f23])).
% 3.28/1.00  
% 3.28/1.00  fof(f13,axiom,(
% 3.28/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 3.28/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f34,plain,(
% 3.28/1.00    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.28/1.00    inference(ennf_transformation,[],[f13])).
% 3.28/1.00  
% 3.28/1.00  fof(f35,plain,(
% 3.28/1.00    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.28/1.00    inference(flattening,[],[f34])).
% 3.28/1.00  
% 3.28/1.00  fof(f82,plain,(
% 3.28/1.00    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f35])).
% 3.28/1.00  
% 3.28/1.00  fof(f91,plain,(
% 3.28/1.00    v2_tdlat_3(sK3)),
% 3.28/1.00    inference(cnf_transformation,[],[f60])).
% 3.28/1.00  
% 3.28/1.00  fof(f2,axiom,(
% 3.28/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.28/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f20,plain,(
% 3.28/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.28/1.00    inference(ennf_transformation,[],[f2])).
% 3.28/1.00  
% 3.28/1.00  fof(f48,plain,(
% 3.28/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.28/1.00    inference(nnf_transformation,[],[f20])).
% 3.28/1.00  
% 3.28/1.00  fof(f49,plain,(
% 3.28/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.28/1.00    inference(rectify,[],[f48])).
% 3.28/1.00  
% 3.28/1.00  fof(f50,plain,(
% 3.28/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.28/1.00    introduced(choice_axiom,[])).
% 3.28/1.00  
% 3.28/1.00  fof(f51,plain,(
% 3.28/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.28/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).
% 3.28/1.00  
% 3.28/1.00  fof(f63,plain,(
% 3.28/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f51])).
% 3.28/1.00  
% 3.28/1.00  fof(f16,axiom,(
% 3.28/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 3.28/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f40,plain,(
% 3.28/1.00    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.28/1.00    inference(ennf_transformation,[],[f16])).
% 3.28/1.00  
% 3.28/1.00  fof(f41,plain,(
% 3.28/1.00    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.28/1.00    inference(flattening,[],[f40])).
% 3.28/1.00  
% 3.28/1.00  fof(f88,plain,(
% 3.28/1.00    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f41])).
% 3.28/1.00  
% 3.28/1.00  fof(f96,plain,(
% 3.28/1.00    ~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)),
% 3.28/1.00    inference(cnf_transformation,[],[f60])).
% 3.28/1.00  
% 3.28/1.00  cnf(c_2867,plain,
% 3.28/1.00      ( ~ v1_zfmisc_1(X0) | v1_zfmisc_1(X1) | X1 != X0 ),
% 3.28/1.00      theory(equality) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_7437,plain,
% 3.28/1.00      ( v1_zfmisc_1(X0)
% 3.28/1.00      | ~ v1_zfmisc_1(u1_struct_0(sK2(X1,sK4)))
% 3.28/1.00      | X0 != u1_struct_0(sK2(X1,sK4)) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_2867]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_12424,plain,
% 3.28/1.00      ( ~ v1_zfmisc_1(u1_struct_0(sK2(X0,sK4)))
% 3.28/1.00      | v1_zfmisc_1(sK4)
% 3.28/1.00      | sK4 != u1_struct_0(sK2(X0,sK4)) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_7437]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_12426,plain,
% 3.28/1.00      ( ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 3.28/1.00      | v1_zfmisc_1(sK4)
% 3.28/1.00      | sK4 != u1_struct_0(sK2(sK3,sK4)) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_12424]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_29,negated_conjecture,
% 3.28/1.00      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 3.28/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3681,plain,
% 3.28/1.00      ( v2_tex_2(sK4,sK3) = iProver_top
% 3.28/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_30,negated_conjecture,
% 3.28/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.28/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3680,plain,
% 3.28/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_23,plain,
% 3.28/1.00      ( ~ v2_tex_2(X0,X1)
% 3.28/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.28/1.00      | v2_struct_0(X1)
% 3.28/1.00      | ~ v2_pre_topc(X1)
% 3.28/1.00      | ~ l1_pre_topc(X1)
% 3.28/1.00      | v1_xboole_0(X0)
% 3.28/1.00      | u1_struct_0(sK2(X1,X0)) = X0 ),
% 3.28/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3687,plain,
% 3.28/1.00      ( u1_struct_0(sK2(X0,X1)) = X1
% 3.28/1.00      | v2_tex_2(X1,X0) != iProver_top
% 3.28/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.28/1.00      | v2_struct_0(X0) = iProver_top
% 3.28/1.00      | v2_pre_topc(X0) != iProver_top
% 3.28/1.00      | l1_pre_topc(X0) != iProver_top
% 3.28/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_5902,plain,
% 3.28/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.28/1.00      | v2_tex_2(sK4,sK3) != iProver_top
% 3.28/1.00      | v2_struct_0(sK3) = iProver_top
% 3.28/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.28/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.28/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_3680,c_3687]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_35,negated_conjecture,
% 3.28/1.00      ( ~ v2_struct_0(sK3) ),
% 3.28/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_36,plain,
% 3.28/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_34,negated_conjecture,
% 3.28/1.00      ( v2_pre_topc(sK3) ),
% 3.28/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_37,plain,
% 3.28/1.00      ( v2_pre_topc(sK3) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_32,negated_conjecture,
% 3.28/1.00      ( l1_pre_topc(sK3) ),
% 3.28/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_39,plain,
% 3.28/1.00      ( l1_pre_topc(sK3) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_31,negated_conjecture,
% 3.28/1.00      ( ~ v1_xboole_0(sK4) ),
% 3.28/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_40,plain,
% 3.28/1.00      ( v1_xboole_0(sK4) != iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_6461,plain,
% 3.28/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.28/1.00      | v2_tex_2(sK4,sK3) != iProver_top ),
% 3.28/1.00      inference(global_propositional_subsumption,
% 3.28/1.00                [status(thm)],
% 3.28/1.00                [c_5902,c_36,c_37,c_39,c_40]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_6467,plain,
% 3.28/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.28/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_3681,c_6461]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_0,plain,
% 3.28/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.28/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3703,plain,
% 3.28/1.00      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.28/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_8,plain,
% 3.28/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.28/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_1,plain,
% 3.28/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.28/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_218,plain,
% 3.28/1.00      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.28/1.00      inference(global_propositional_subsumption,[status(thm)],[c_8,c_1]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_219,plain,
% 3.28/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.28/1.00      inference(renaming,[status(thm)],[c_218]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3674,plain,
% 3.28/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.28/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_219]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4437,plain,
% 3.28/1.00      ( m1_subset_1(sK0(X0),X0) = iProver_top
% 3.28/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_3703,c_3674]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_16,plain,
% 3.28/1.00      ( ~ m1_subset_1(X0,X1)
% 3.28/1.00      | v1_xboole_0(X1)
% 3.28/1.00      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.28/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3690,plain,
% 3.28/1.00      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 3.28/1.00      | m1_subset_1(X1,X0) != iProver_top
% 3.28/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_6095,plain,
% 3.28/1.00      ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
% 3.28/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_4437,c_3690]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3679,plain,
% 3.28/1.00      ( v1_xboole_0(sK4) != iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_6839,plain,
% 3.28/1.00      ( k6_domain_1(sK4,sK0(sK4)) = k1_tarski(sK0(sK4)) ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_6095,c_3679]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_15,plain,
% 3.28/1.00      ( ~ m1_subset_1(X0,X1)
% 3.28/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 3.28/1.00      | v1_xboole_0(X1) ),
% 3.28/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3691,plain,
% 3.28/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.28/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 3.28/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_6925,plain,
% 3.28/1.00      ( m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4)) = iProver_top
% 3.28/1.00      | m1_subset_1(sK0(sK4),sK4) != iProver_top
% 3.28/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_6839,c_3691]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3978,plain,
% 3.28/1.00      ( r2_hidden(sK0(sK4),sK4) | v1_xboole_0(sK4) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3979,plain,
% 3.28/1.00      ( r2_hidden(sK0(sK4),sK4) = iProver_top
% 3.28/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_3978]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4178,plain,
% 3.28/1.00      ( m1_subset_1(X0,sK4) | ~ r2_hidden(X0,sK4) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_219]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4419,plain,
% 3.28/1.00      ( m1_subset_1(sK0(sK4),sK4) | ~ r2_hidden(sK0(sK4),sK4) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_4178]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4420,plain,
% 3.28/1.00      ( m1_subset_1(sK0(sK4),sK4) = iProver_top
% 3.28/1.00      | r2_hidden(sK0(sK4),sK4) != iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_4419]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_7046,plain,
% 3.28/1.00      ( m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4)) = iProver_top ),
% 3.28/1.00      inference(global_propositional_subsumption,
% 3.28/1.00                [status(thm)],
% 3.28/1.00                [c_6925,c_40,c_3979,c_4420]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_11,plain,
% 3.28/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.28/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3693,plain,
% 3.28/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.28/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_7053,plain,
% 3.28/1.00      ( r1_tarski(k1_tarski(sK0(sK4)),sK4) = iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_7046,c_3693]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_22,plain,
% 3.28/1.00      ( ~ r1_tarski(X0,X1)
% 3.28/1.00      | ~ v1_zfmisc_1(X1)
% 3.28/1.00      | v1_xboole_0(X0)
% 3.28/1.00      | v1_xboole_0(X1)
% 3.28/1.00      | X1 = X0 ),
% 3.28/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3688,plain,
% 3.28/1.00      ( X0 = X1
% 3.28/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.28/1.00      | v1_zfmisc_1(X0) != iProver_top
% 3.28/1.00      | v1_xboole_0(X1) = iProver_top
% 3.28/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_7148,plain,
% 3.28/1.00      ( k1_tarski(sK0(sK4)) = sK4
% 3.28/1.00      | v1_zfmisc_1(sK4) != iProver_top
% 3.28/1.00      | v1_xboole_0(k1_tarski(sK0(sK4))) = iProver_top
% 3.28/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_7053,c_3688]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_8325,plain,
% 3.28/1.00      ( v1_xboole_0(k1_tarski(sK0(sK4))) = iProver_top
% 3.28/1.00      | v1_zfmisc_1(sK4) != iProver_top
% 3.28/1.00      | k1_tarski(sK0(sK4)) = sK4 ),
% 3.28/1.00      inference(global_propositional_subsumption,
% 3.28/1.00                [status(thm)],
% 3.28/1.00                [c_7148,c_40]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_8326,plain,
% 3.28/1.00      ( k1_tarski(sK0(sK4)) = sK4
% 3.28/1.00      | v1_zfmisc_1(sK4) != iProver_top
% 3.28/1.00      | v1_xboole_0(k1_tarski(sK0(sK4))) = iProver_top ),
% 3.28/1.00      inference(renaming,[status(thm)],[c_8325]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_5,plain,
% 3.28/1.00      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 3.28/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3698,plain,
% 3.28/1.00      ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_8332,plain,
% 3.28/1.00      ( k1_tarski(sK0(sK4)) = sK4 | v1_zfmisc_1(sK4) != iProver_top ),
% 3.28/1.00      inference(forward_subsumption_resolution,
% 3.28/1.00                [status(thm)],
% 3.28/1.00                [c_8326,c_3698]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_8334,plain,
% 3.28/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4 | k1_tarski(sK0(sK4)) = sK4 ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_6467,c_8332]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_19,plain,
% 3.28/1.00      ( v2_struct_0(X0)
% 3.28/1.00      | ~ v1_tdlat_3(X0)
% 3.28/1.00      | ~ v2_tdlat_3(X0)
% 3.28/1.00      | ~ v2_pre_topc(X0)
% 3.28/1.00      | v7_struct_0(X0)
% 3.28/1.00      | ~ l1_pre_topc(X0) ),
% 3.28/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_17,plain,
% 3.28/1.00      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 3.28/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_202,plain,
% 3.28/1.00      ( ~ v2_tdlat_3(X0)
% 3.28/1.00      | ~ v1_tdlat_3(X0)
% 3.28/1.00      | v2_struct_0(X0)
% 3.28/1.00      | v7_struct_0(X0)
% 3.28/1.00      | ~ l1_pre_topc(X0) ),
% 3.28/1.00      inference(global_propositional_subsumption,
% 3.28/1.00                [status(thm)],
% 3.28/1.00                [c_19,c_17]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_203,plain,
% 3.28/1.00      ( v2_struct_0(X0)
% 3.28/1.00      | ~ v1_tdlat_3(X0)
% 3.28/1.00      | ~ v2_tdlat_3(X0)
% 3.28/1.00      | v7_struct_0(X0)
% 3.28/1.00      | ~ l1_pre_topc(X0) ),
% 3.28/1.00      inference(renaming,[status(thm)],[c_202]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_12,plain,
% 3.28/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.28/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_14,plain,
% 3.28/1.00      ( ~ v7_struct_0(X0)
% 3.28/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.28/1.00      | ~ l1_struct_0(X0) ),
% 3.28/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_465,plain,
% 3.28/1.00      ( ~ v7_struct_0(X0)
% 3.28/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.28/1.00      | ~ l1_pre_topc(X0) ),
% 3.28/1.00      inference(resolution,[status(thm)],[c_12,c_14]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_483,plain,
% 3.28/1.00      ( v2_struct_0(X0)
% 3.28/1.00      | ~ v1_tdlat_3(X0)
% 3.28/1.00      | ~ v2_tdlat_3(X0)
% 3.28/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.28/1.00      | ~ l1_pre_topc(X0) ),
% 3.28/1.00      inference(resolution,[status(thm)],[c_203,c_465]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3673,plain,
% 3.28/1.00      ( v2_struct_0(X0) = iProver_top
% 3.28/1.00      | v1_tdlat_3(X0) != iProver_top
% 3.28/1.00      | v2_tdlat_3(X0) != iProver_top
% 3.28/1.00      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
% 3.28/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_8949,plain,
% 3.28/1.00      ( k1_tarski(sK0(sK4)) = sK4
% 3.28/1.00      | v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 3.28/1.00      | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 3.28/1.00      | v2_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 3.28/1.00      | v1_zfmisc_1(sK4) = iProver_top
% 3.28/1.00      | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_8334,c_3673]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_42,plain,
% 3.28/1.00      ( v2_tex_2(sK4,sK3) = iProver_top
% 3.28/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_26,plain,
% 3.28/1.00      ( ~ v2_tex_2(X0,X1)
% 3.28/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.28/1.00      | v2_struct_0(X1)
% 3.28/1.00      | ~ v2_struct_0(sK2(X1,X0))
% 3.28/1.00      | ~ v2_pre_topc(X1)
% 3.28/1.00      | ~ l1_pre_topc(X1)
% 3.28/1.00      | v1_xboole_0(X0) ),
% 3.28/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_282,plain,
% 3.28/1.00      ( v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3) ),
% 3.28/1.00      inference(prop_impl,[status(thm)],[c_29]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_283,plain,
% 3.28/1.00      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 3.28/1.00      inference(renaming,[status(thm)],[c_282]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_981,plain,
% 3.28/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.28/1.00      | v2_struct_0(X1)
% 3.28/1.00      | ~ v2_struct_0(sK2(X1,X0))
% 3.28/1.00      | ~ v2_pre_topc(X1)
% 3.28/1.00      | v1_zfmisc_1(sK4)
% 3.28/1.00      | ~ l1_pre_topc(X1)
% 3.28/1.00      | v1_xboole_0(X0)
% 3.28/1.00      | sK3 != X1
% 3.28/1.00      | sK4 != X0 ),
% 3.28/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_283]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_982,plain,
% 3.28/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.28/1.00      | ~ v2_struct_0(sK2(sK3,sK4))
% 3.28/1.00      | v2_struct_0(sK3)
% 3.28/1.00      | ~ v2_pre_topc(sK3)
% 3.28/1.00      | v1_zfmisc_1(sK4)
% 3.28/1.00      | ~ l1_pre_topc(sK3)
% 3.28/1.00      | v1_xboole_0(sK4) ),
% 3.28/1.00      inference(unflattening,[status(thm)],[c_981]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_984,plain,
% 3.28/1.00      ( ~ v2_struct_0(sK2(sK3,sK4)) | v1_zfmisc_1(sK4) ),
% 3.28/1.00      inference(global_propositional_subsumption,
% 3.28/1.00                [status(thm)],
% 3.28/1.00                [c_982,c_35,c_34,c_32,c_31,c_30]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_986,plain,
% 3.28/1.00      ( v2_struct_0(sK2(sK3,sK4)) != iProver_top
% 3.28/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_984]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_25,plain,
% 3.28/1.00      ( ~ v2_tex_2(X0,X1)
% 3.28/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.28/1.00      | v2_struct_0(X1)
% 3.28/1.00      | v1_tdlat_3(sK2(X1,X0))
% 3.28/1.00      | ~ v2_pre_topc(X1)
% 3.28/1.00      | ~ l1_pre_topc(X1)
% 3.28/1.00      | v1_xboole_0(X0) ),
% 3.28/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_995,plain,
% 3.28/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.28/1.00      | v2_struct_0(X1)
% 3.28/1.00      | v1_tdlat_3(sK2(X1,X0))
% 3.28/1.00      | ~ v2_pre_topc(X1)
% 3.28/1.00      | v1_zfmisc_1(sK4)
% 3.28/1.00      | ~ l1_pre_topc(X1)
% 3.28/1.00      | v1_xboole_0(X0)
% 3.28/1.00      | sK3 != X1
% 3.28/1.00      | sK4 != X0 ),
% 3.28/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_283]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_996,plain,
% 3.28/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.28/1.00      | v2_struct_0(sK3)
% 3.28/1.00      | v1_tdlat_3(sK2(sK3,sK4))
% 3.28/1.00      | ~ v2_pre_topc(sK3)
% 3.28/1.00      | v1_zfmisc_1(sK4)
% 3.28/1.00      | ~ l1_pre_topc(sK3)
% 3.28/1.00      | v1_xboole_0(sK4) ),
% 3.28/1.00      inference(unflattening,[status(thm)],[c_995]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_998,plain,
% 3.28/1.00      ( v1_tdlat_3(sK2(sK3,sK4)) | v1_zfmisc_1(sK4) ),
% 3.28/1.00      inference(global_propositional_subsumption,
% 3.28/1.00                [status(thm)],
% 3.28/1.00                [c_996,c_35,c_34,c_32,c_31,c_30]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_1000,plain,
% 3.28/1.00      ( v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
% 3.28/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_998]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_24,plain,
% 3.28/1.00      ( ~ v2_tex_2(X0,X1)
% 3.28/1.00      | m1_pre_topc(sK2(X1,X0),X1)
% 3.28/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.28/1.00      | v2_struct_0(X1)
% 3.28/1.00      | ~ v2_pre_topc(X1)
% 3.28/1.00      | ~ l1_pre_topc(X1)
% 3.28/1.00      | v1_xboole_0(X0) ),
% 3.28/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3686,plain,
% 3.28/1.00      ( v2_tex_2(X0,X1) != iProver_top
% 3.28/1.00      | m1_pre_topc(sK2(X1,X0),X1) = iProver_top
% 3.28/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.28/1.00      | v2_struct_0(X1) = iProver_top
% 3.28/1.00      | v2_pre_topc(X1) != iProver_top
% 3.28/1.00      | l1_pre_topc(X1) != iProver_top
% 3.28/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_6035,plain,
% 3.28/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.28/1.00      | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
% 3.28/1.00      | v2_struct_0(sK3) = iProver_top
% 3.28/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.28/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.28/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_3680,c_3686]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_6587,plain,
% 3.28/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.28/1.00      | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top ),
% 3.28/1.00      inference(global_propositional_subsumption,
% 3.28/1.00                [status(thm)],
% 3.28/1.00                [c_6035,c_36,c_37,c_39,c_40]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_13,plain,
% 3.28/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.28/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3692,plain,
% 3.28/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.28/1.00      | l1_pre_topc(X1) != iProver_top
% 3.28/1.00      | l1_pre_topc(X0) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_6593,plain,
% 3.28/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.28/1.00      | l1_pre_topc(sK2(sK3,sK4)) = iProver_top
% 3.28/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_6587,c_3692]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_21,plain,
% 3.28/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.28/1.00      | v2_struct_0(X1)
% 3.28/1.00      | ~ v2_tdlat_3(X1)
% 3.28/1.00      | v2_tdlat_3(X0)
% 3.28/1.00      | ~ v2_pre_topc(X1)
% 3.28/1.00      | ~ l1_pre_topc(X1) ),
% 3.28/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_1225,plain,
% 3.28/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.28/1.00      | v2_struct_0(X1)
% 3.28/1.00      | ~ v2_tdlat_3(X2)
% 3.28/1.00      | ~ v2_tdlat_3(X1)
% 3.28/1.00      | v2_tdlat_3(X0)
% 3.28/1.00      | ~ l1_pre_topc(X2)
% 3.28/1.00      | ~ l1_pre_topc(X1)
% 3.28/1.00      | X1 != X2 ),
% 3.28/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_1226,plain,
% 3.28/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.28/1.00      | v2_struct_0(X1)
% 3.28/1.00      | ~ v2_tdlat_3(X1)
% 3.28/1.00      | v2_tdlat_3(X0)
% 3.28/1.00      | ~ l1_pre_topc(X1) ),
% 3.28/1.00      inference(unflattening,[status(thm)],[c_1225]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3672,plain,
% 3.28/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.28/1.00      | v2_struct_0(X1) = iProver_top
% 3.28/1.00      | v2_tdlat_3(X1) != iProver_top
% 3.28/1.00      | v2_tdlat_3(X0) = iProver_top
% 3.28/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_1226]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_6594,plain,
% 3.28/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.28/1.00      | v2_struct_0(sK3) = iProver_top
% 3.28/1.00      | v2_tdlat_3(sK2(sK3,sK4)) = iProver_top
% 3.28/1.00      | v2_tdlat_3(sK3) != iProver_top
% 3.28/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_6587,c_3672]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_33,negated_conjecture,
% 3.28/1.00      ( v2_tdlat_3(sK3) ),
% 3.28/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_38,plain,
% 3.28/1.00      ( v2_tdlat_3(sK3) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_6697,plain,
% 3.28/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.28/1.00      | v2_tdlat_3(sK2(sK3,sK4)) = iProver_top ),
% 3.28/1.00      inference(global_propositional_subsumption,
% 3.28/1.00                [status(thm)],
% 3.28/1.00                [c_6594,c_36,c_38,c_39]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_9156,plain,
% 3.28/1.00      ( k1_tarski(sK0(sK4)) = sK4 ),
% 3.28/1.00      inference(global_propositional_subsumption,
% 3.28/1.00                [status(thm)],
% 3.28/1.00                [c_8949,c_39,c_42,c_986,c_1000,c_6593,c_6697,c_8332]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4352,plain,
% 3.28/1.00      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_3680,c_3693]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4,plain,
% 3.28/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.28/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3699,plain,
% 3.28/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.28/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.28/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_5045,plain,
% 3.28/1.00      ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
% 3.28/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_4352,c_3699]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_5446,plain,
% 3.28/1.00      ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
% 3.28/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_5045,c_3674]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_5707,plain,
% 3.28/1.00      ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
% 3.28/1.00      | r2_hidden(X0,sK4) != iProver_top
% 3.28/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_5446,c_3690]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4127,plain,
% 3.28/1.00      ( ~ r1_tarski(sK4,X0)
% 3.28/1.00      | r2_hidden(sK0(sK4),X0)
% 3.28/1.00      | ~ r2_hidden(sK0(sK4),sK4) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4677,plain,
% 3.28/1.00      ( ~ r1_tarski(sK4,u1_struct_0(X0))
% 3.28/1.00      | r2_hidden(sK0(sK4),u1_struct_0(X0))
% 3.28/1.00      | ~ r2_hidden(sK0(sK4),sK4) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_4127]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4679,plain,
% 3.28/1.00      ( r1_tarski(sK4,u1_struct_0(X0)) != iProver_top
% 3.28/1.00      | r2_hidden(sK0(sK4),u1_struct_0(X0)) = iProver_top
% 3.28/1.00      | r2_hidden(sK0(sK4),sK4) != iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_4677]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4681,plain,
% 3.28/1.00      ( r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
% 3.28/1.00      | r2_hidden(sK0(sK4),u1_struct_0(sK3)) = iProver_top
% 3.28/1.00      | r2_hidden(sK0(sK4),sK4) != iProver_top ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_4679]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4664,plain,
% 3.28/1.00      ( ~ r2_hidden(sK0(sK4),X0) | ~ v1_xboole_0(X0) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_5220,plain,
% 3.28/1.00      ( ~ r2_hidden(sK0(sK4),u1_struct_0(X0))
% 3.28/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_4664]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_5221,plain,
% 3.28/1.00      ( r2_hidden(sK0(sK4),u1_struct_0(X0)) != iProver_top
% 3.28/1.00      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_5220]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_5223,plain,
% 3.28/1.00      ( r2_hidden(sK0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.28/1.00      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_5221]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_8299,plain,
% 3.28/1.00      ( r2_hidden(X0,sK4) != iProver_top
% 3.28/1.00      | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
% 3.28/1.00      inference(global_propositional_subsumption,
% 3.28/1.00                [status(thm)],
% 3.28/1.00                [c_5707,c_40,c_3979,c_4352,c_4681,c_5223]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_8300,plain,
% 3.28/1.00      ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
% 3.28/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.28/1.00      inference(renaming,[status(thm)],[c_8299]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_8307,plain,
% 3.28/1.00      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4))
% 3.28/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_3703,c_8300]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_8560,plain,
% 3.28/1.00      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
% 3.28/1.00      inference(global_propositional_subsumption,
% 3.28/1.00                [status(thm)],
% 3.28/1.00                [c_8307,c_40]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_9160,plain,
% 3.28/1.00      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = sK4 ),
% 3.28/1.00      inference(demodulation,[status(thm)],[c_9156,c_8560]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_27,plain,
% 3.28/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.28/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.28/1.00      | v2_struct_0(X0)
% 3.28/1.00      | ~ v2_pre_topc(X0)
% 3.28/1.00      | ~ l1_pre_topc(X0) ),
% 3.28/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3683,plain,
% 3.28/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) = iProver_top
% 3.28/1.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.28/1.00      | v2_struct_0(X0) = iProver_top
% 3.28/1.00      | v2_pre_topc(X0) != iProver_top
% 3.28/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_10103,plain,
% 3.28/1.00      ( v2_tex_2(sK4,sK3) = iProver_top
% 3.28/1.00      | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.28/1.00      | v2_struct_0(sK3) = iProver_top
% 3.28/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.28/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_9160,c_3683]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_10114,plain,
% 3.28/1.00      ( v2_tex_2(sK4,sK3)
% 3.28/1.00      | ~ m1_subset_1(sK0(sK4),u1_struct_0(sK3))
% 3.28/1.00      | v2_struct_0(sK3)
% 3.28/1.00      | ~ v2_pre_topc(sK3)
% 3.28/1.00      | ~ l1_pre_topc(sK3) ),
% 3.28/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_10103]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_6699,plain,
% 3.28/1.00      ( ~ v2_tex_2(sK4,sK3) | v2_tdlat_3(sK2(sK3,sK4)) ),
% 3.28/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6697]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_6611,plain,
% 3.28/1.00      ( ~ v2_tex_2(sK4,sK3)
% 3.28/1.00      | l1_pre_topc(sK2(sK3,sK4))
% 3.28/1.00      | ~ l1_pre_topc(sK3) ),
% 3.28/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6593]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_2859,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4162,plain,
% 3.28/1.00      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_2859]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4423,plain,
% 3.28/1.00      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_4162]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_6558,plain,
% 3.28/1.00      ( u1_struct_0(sK2(X0,sK4)) != sK4
% 3.28/1.00      | sK4 = u1_struct_0(sK2(X0,sK4))
% 3.28/1.00      | sK4 != sK4 ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_4423]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_6564,plain,
% 3.28/1.00      ( u1_struct_0(sK2(sK3,sK4)) != sK4
% 3.28/1.00      | sK4 = u1_struct_0(sK2(sK3,sK4))
% 3.28/1.00      | sK4 != sK4 ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_6558]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_6547,plain,
% 3.28/1.00      ( v2_struct_0(sK2(X0,sK4))
% 3.28/1.00      | ~ v1_tdlat_3(sK2(X0,sK4))
% 3.28/1.00      | ~ v2_tdlat_3(sK2(X0,sK4))
% 3.28/1.00      | v1_zfmisc_1(u1_struct_0(sK2(X0,sK4)))
% 3.28/1.00      | ~ l1_pre_topc(sK2(X0,sK4)) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_483]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_6549,plain,
% 3.28/1.00      ( v2_struct_0(sK2(sK3,sK4))
% 3.28/1.00      | ~ v1_tdlat_3(sK2(sK3,sK4))
% 3.28/1.00      | ~ v2_tdlat_3(sK2(sK3,sK4))
% 3.28/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 3.28/1.00      | ~ l1_pre_topc(sK2(sK3,sK4)) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_6547]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3684,plain,
% 3.28/1.00      ( v2_tex_2(X0,X1) != iProver_top
% 3.28/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.28/1.00      | v2_struct_0(X1) = iProver_top
% 3.28/1.00      | v2_struct_0(sK2(X1,X0)) != iProver_top
% 3.28/1.00      | v2_pre_topc(X1) != iProver_top
% 3.28/1.00      | l1_pre_topc(X1) != iProver_top
% 3.28/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_5841,plain,
% 3.28/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.28/1.00      | v2_struct_0(sK2(sK3,sK4)) != iProver_top
% 3.28/1.00      | v2_struct_0(sK3) = iProver_top
% 3.28/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.28/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.28/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_3680,c_3684]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_6530,plain,
% 3.28/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.28/1.00      | v2_struct_0(sK2(sK3,sK4)) != iProver_top ),
% 3.28/1.00      inference(global_propositional_subsumption,
% 3.28/1.00                [status(thm)],
% 3.28/1.00                [c_5841,c_36,c_37,c_39,c_40]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_6532,plain,
% 3.28/1.00      ( ~ v2_tex_2(sK4,sK3) | ~ v2_struct_0(sK2(sK3,sK4)) ),
% 3.28/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6530]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3685,plain,
% 3.28/1.00      ( v2_tex_2(X0,X1) != iProver_top
% 3.28/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.28/1.00      | v2_struct_0(X1) = iProver_top
% 3.28/1.00      | v1_tdlat_3(sK2(X1,X0)) = iProver_top
% 3.28/1.00      | v2_pre_topc(X1) != iProver_top
% 3.28/1.00      | l1_pre_topc(X1) != iProver_top
% 3.28/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_5255,plain,
% 3.28/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.28/1.00      | v2_struct_0(sK3) = iProver_top
% 3.28/1.00      | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
% 3.28/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.28/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.28/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.28/1.00      inference(superposition,[status(thm)],[c_3680,c_3685]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_5378,plain,
% 3.28/1.00      ( v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
% 3.28/1.00      | v2_tex_2(sK4,sK3) != iProver_top ),
% 3.28/1.00      inference(global_propositional_subsumption,
% 3.28/1.00                [status(thm)],
% 3.28/1.00                [c_5255,c_36,c_37,c_39,c_40]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_5379,plain,
% 3.28/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.28/1.00      | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top ),
% 3.28/1.00      inference(renaming,[status(thm)],[c_5378]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_5380,plain,
% 3.28/1.00      ( ~ v2_tex_2(sK4,sK3) | v1_tdlat_3(sK2(sK3,sK4)) ),
% 3.28/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5379]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4058,plain,
% 3.28/1.00      ( m1_subset_1(X0,u1_struct_0(X1))
% 3.28/1.00      | ~ r2_hidden(X0,u1_struct_0(X1)) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_219]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4678,plain,
% 3.28/1.00      ( m1_subset_1(sK0(sK4),u1_struct_0(X0))
% 3.28/1.00      | ~ r2_hidden(sK0(sK4),u1_struct_0(X0)) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_4058]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4683,plain,
% 3.28/1.00      ( m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
% 3.28/1.00      | r2_hidden(sK0(sK4),u1_struct_0(X0)) != iProver_top ),
% 3.28/1.00      inference(predicate_to_equality,[status(thm)],[c_4678]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4685,plain,
% 3.28/1.00      ( m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
% 3.28/1.00      | r2_hidden(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_4683]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4684,plain,
% 3.28/1.00      ( m1_subset_1(sK0(sK4),u1_struct_0(sK3))
% 3.28/1.00      | ~ r2_hidden(sK0(sK4),u1_struct_0(sK3)) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_4678]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4680,plain,
% 3.28/1.00      ( ~ r1_tarski(sK4,u1_struct_0(sK3))
% 3.28/1.00      | r2_hidden(sK0(sK4),u1_struct_0(sK3))
% 3.28/1.00      | ~ r2_hidden(sK0(sK4),sK4) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_4677]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_2858,plain,( X0 = X0 ),theory(equality) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4424,plain,
% 3.28/1.00      ( sK4 = sK4 ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_2858]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4353,plain,
% 3.28/1.00      ( r1_tarski(sK4,u1_struct_0(sK3)) ),
% 3.28/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4352]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_28,negated_conjecture,
% 3.28/1.00      ( ~ v2_tex_2(sK4,sK3) | ~ v1_zfmisc_1(sK4) ),
% 3.28/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(contradiction,plain,
% 3.28/1.00      ( $false ),
% 3.28/1.00      inference(minisat,
% 3.28/1.00                [status(thm)],
% 3.28/1.00                [c_12426,c_10114,c_10103,c_6699,c_6611,c_6564,c_6549,
% 3.28/1.00                 c_6532,c_6461,c_5380,c_4685,c_4684,c_4681,c_4680,c_4424,
% 3.28/1.00                 c_4353,c_4352,c_3979,c_3978,c_28,c_40,c_31,c_39,c_32,
% 3.28/1.00                 c_37,c_34,c_36,c_35]) ).
% 3.28/1.00  
% 3.28/1.00  
% 3.28/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.28/1.00  
% 3.28/1.00  ------                               Statistics
% 3.28/1.00  
% 3.28/1.00  ------ General
% 3.28/1.00  
% 3.28/1.00  abstr_ref_over_cycles:                  0
% 3.28/1.00  abstr_ref_under_cycles:                 0
% 3.28/1.00  gc_basic_clause_elim:                   0
% 3.28/1.00  forced_gc_time:                         0
% 3.28/1.00  parsing_time:                           0.008
% 3.28/1.00  unif_index_cands_time:                  0.
% 3.28/1.00  unif_index_add_time:                    0.
% 3.28/1.00  orderings_time:                         0.
% 3.28/1.00  out_proof_time:                         0.01
% 3.28/1.00  total_time:                             0.288
% 3.28/1.00  num_of_symbols:                         54
% 3.28/1.00  num_of_terms:                           7585
% 3.28/1.00  
% 3.28/1.00  ------ Preprocessing
% 3.28/1.00  
% 3.28/1.00  num_of_splits:                          0
% 3.28/1.00  num_of_split_atoms:                     0
% 3.28/1.00  num_of_reused_defs:                     0
% 3.28/1.00  num_eq_ax_congr_red:                    35
% 3.28/1.00  num_of_sem_filtered_clauses:            1
% 3.28/1.00  num_of_subtypes:                        0
% 3.28/1.00  monotx_restored_types:                  0
% 3.28/1.00  sat_num_of_epr_types:                   0
% 3.28/1.00  sat_num_of_non_cyclic_types:            0
% 3.28/1.00  sat_guarded_non_collapsed_types:        0
% 3.28/1.00  num_pure_diseq_elim:                    0
% 3.28/1.00  simp_replaced_by:                       0
% 3.28/1.00  res_preprocessed:                       163
% 3.28/1.00  prep_upred:                             0
% 3.28/1.00  prep_unflattend:                        81
% 3.28/1.00  smt_new_axioms:                         0
% 3.28/1.00  pred_elim_cands:                        12
% 3.28/1.00  pred_elim:                              2
% 3.28/1.00  pred_elim_cl:                           2
% 3.28/1.00  pred_elim_cycles:                       16
% 3.28/1.00  merged_defs:                            16
% 3.28/1.00  merged_defs_ncl:                        0
% 3.28/1.00  bin_hyper_res:                          16
% 3.28/1.00  prep_cycles:                            4
% 3.28/1.00  pred_elim_time:                         0.034
% 3.28/1.00  splitting_time:                         0.
% 3.28/1.00  sem_filter_time:                        0.
% 3.28/1.00  monotx_time:                            0.001
% 3.28/1.00  subtype_inf_time:                       0.
% 3.28/1.00  
% 3.28/1.00  ------ Problem properties
% 3.28/1.00  
% 3.28/1.00  clauses:                                32
% 3.28/1.00  conjectures:                            8
% 3.28/1.00  epr:                                    17
% 3.28/1.00  horn:                                   18
% 3.28/1.00  ground:                                 8
% 3.28/1.00  unary:                                  7
% 3.28/1.00  binary:                                 9
% 3.28/1.00  lits:                                   97
% 3.28/1.00  lits_eq:                                3
% 3.28/1.00  fd_pure:                                0
% 3.28/1.00  fd_pseudo:                              0
% 3.28/1.00  fd_cond:                                0
% 3.28/1.00  fd_pseudo_cond:                         1
% 3.28/1.00  ac_symbols:                             0
% 3.28/1.00  
% 3.28/1.00  ------ Propositional Solver
% 3.28/1.00  
% 3.28/1.00  prop_solver_calls:                      29
% 3.28/1.00  prop_fast_solver_calls:                 2038
% 3.28/1.00  smt_solver_calls:                       0
% 3.28/1.00  smt_fast_solver_calls:                  0
% 3.28/1.00  prop_num_of_clauses:                    3807
% 3.28/1.00  prop_preprocess_simplified:             9197
% 3.28/1.00  prop_fo_subsumed:                       170
% 3.28/1.00  prop_solver_time:                       0.
% 3.28/1.00  smt_solver_time:                        0.
% 3.28/1.00  smt_fast_solver_time:                   0.
% 3.28/1.00  prop_fast_solver_time:                  0.
% 3.28/1.00  prop_unsat_core_time:                   0.
% 3.28/1.00  
% 3.28/1.00  ------ QBF
% 3.28/1.00  
% 3.28/1.00  qbf_q_res:                              0
% 3.28/1.00  qbf_num_tautologies:                    0
% 3.28/1.00  qbf_prep_cycles:                        0
% 3.28/1.00  
% 3.28/1.00  ------ BMC1
% 3.28/1.00  
% 3.28/1.00  bmc1_current_bound:                     -1
% 3.28/1.00  bmc1_last_solved_bound:                 -1
% 3.28/1.00  bmc1_unsat_core_size:                   -1
% 3.28/1.00  bmc1_unsat_core_parents_size:           -1
% 3.28/1.00  bmc1_merge_next_fun:                    0
% 3.28/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.28/1.00  
% 3.28/1.00  ------ Instantiation
% 3.28/1.00  
% 3.28/1.00  inst_num_of_clauses:                    846
% 3.28/1.00  inst_num_in_passive:                    342
% 3.28/1.00  inst_num_in_active:                     440
% 3.28/1.00  inst_num_in_unprocessed:                63
% 3.28/1.00  inst_num_of_loops:                      658
% 3.28/1.00  inst_num_of_learning_restarts:          0
% 3.28/1.00  inst_num_moves_active_passive:          212
% 3.28/1.00  inst_lit_activity:                      0
% 3.28/1.00  inst_lit_activity_moves:                0
% 3.28/1.00  inst_num_tautologies:                   0
% 3.28/1.00  inst_num_prop_implied:                  0
% 3.28/1.00  inst_num_existing_simplified:           0
% 3.28/1.00  inst_num_eq_res_simplified:             0
% 3.28/1.00  inst_num_child_elim:                    0
% 3.28/1.00  inst_num_of_dismatching_blockings:      379
% 3.28/1.00  inst_num_of_non_proper_insts:           986
% 3.28/1.00  inst_num_of_duplicates:                 0
% 3.28/1.00  inst_inst_num_from_inst_to_res:         0
% 3.28/1.00  inst_dismatching_checking_time:         0.
% 3.28/1.00  
% 3.28/1.00  ------ Resolution
% 3.28/1.00  
% 3.28/1.00  res_num_of_clauses:                     0
% 3.28/1.00  res_num_in_passive:                     0
% 3.28/1.00  res_num_in_active:                      0
% 3.28/1.00  res_num_of_loops:                       167
% 3.28/1.00  res_forward_subset_subsumed:            123
% 3.28/1.00  res_backward_subset_subsumed:           0
% 3.28/1.00  res_forward_subsumed:                   0
% 3.28/1.00  res_backward_subsumed:                  1
% 3.28/1.00  res_forward_subsumption_resolution:     2
% 3.28/1.00  res_backward_subsumption_resolution:    0
% 3.28/1.00  res_clause_to_clause_subsumption:       571
% 3.28/1.00  res_orphan_elimination:                 0
% 3.28/1.00  res_tautology_del:                      118
% 3.28/1.00  res_num_eq_res_simplified:              0
% 3.28/1.00  res_num_sel_changes:                    0
% 3.28/1.00  res_moves_from_active_to_pass:          0
% 3.28/1.00  
% 3.28/1.00  ------ Superposition
% 3.28/1.00  
% 3.28/1.00  sup_time_total:                         0.
% 3.28/1.00  sup_time_generating:                    0.
% 3.28/1.00  sup_time_sim_full:                      0.
% 3.28/1.00  sup_time_sim_immed:                     0.
% 3.28/1.00  
% 3.28/1.00  sup_num_of_clauses:                     227
% 3.28/1.00  sup_num_in_active:                      118
% 3.28/1.00  sup_num_in_passive:                     109
% 3.28/1.00  sup_num_of_loops:                       130
% 3.28/1.00  sup_fw_superposition:                   113
% 3.28/1.00  sup_bw_superposition:                   210
% 3.28/1.00  sup_immediate_simplified:               56
% 3.28/1.00  sup_given_eliminated:                   0
% 3.28/1.00  comparisons_done:                       0
% 3.28/1.00  comparisons_avoided:                    0
% 3.28/1.00  
% 3.28/1.00  ------ Simplifications
% 3.28/1.00  
% 3.28/1.00  
% 3.28/1.00  sim_fw_subset_subsumed:                 36
% 3.28/1.00  sim_bw_subset_subsumed:                 13
% 3.28/1.00  sim_fw_subsumed:                        9
% 3.28/1.00  sim_bw_subsumed:                        0
% 3.28/1.00  sim_fw_subsumption_res:                 7
% 3.28/1.00  sim_bw_subsumption_res:                 0
% 3.28/1.00  sim_tautology_del:                      19
% 3.28/1.00  sim_eq_tautology_del:                   7
% 3.28/1.00  sim_eq_res_simp:                        0
% 3.28/1.00  sim_fw_demodulated:                     0
% 3.28/1.00  sim_bw_demodulated:                     10
% 3.28/1.00  sim_light_normalised:                   17
% 3.28/1.00  sim_joinable_taut:                      0
% 3.28/1.00  sim_joinable_simp:                      0
% 3.28/1.00  sim_ac_normalised:                      0
% 3.28/1.00  sim_smt_subsumption:                    0
% 3.28/1.00  
%------------------------------------------------------------------------------
