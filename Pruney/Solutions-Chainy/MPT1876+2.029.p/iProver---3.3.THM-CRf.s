%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:53 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  211 (2828 expanded)
%              Number of clauses        :  124 ( 713 expanded)
%              Number of leaves         :   22 ( 637 expanded)
%              Depth                    :   25
%              Number of atoms          :  821 (19205 expanded)
%              Number of equality atoms :  237 (1181 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

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
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f61,plain,(
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

fof(f60,plain,
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

fof(f62,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f59,f61,f60])).

fof(f99,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f98,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f62])).

fof(f16,axiom,(
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

fof(f20,plain,(
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
    inference(pure_predicate_removal,[],[f16])).

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
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f56,plain,(
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

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f56])).

fof(f91,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f94,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f96,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f97,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).

fof(f64,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f87,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f84,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f82,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f77,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f79,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f78,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f51])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f100,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_31,negated_conjecture,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_5892,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_5891,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_25,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_5898,plain,
    ( u1_struct_0(sK2(X0,X1)) = X1
    | v2_tex_2(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8040,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5891,c_5898])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_38,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_39,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_41,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_42,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8324,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8040,c_38,c_39,c_41,c_42])).

cnf(c_8330,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5892,c_8324])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_5916,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_5910,plain,
    ( r1_tarski(k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_24,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_5899,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7882,plain,
    ( k1_tarski(X0) = X1
    | r2_hidden(X0,X1) != iProver_top
    | v1_zfmisc_1(X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k1_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5910,c_5899])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_104,plain,
    ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_114,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12395,plain,
    ( k1_tarski(X0) = X1
    | r2_hidden(X0,X1) != iProver_top
    | v1_zfmisc_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7882,c_104,c_114])).

cnf(c_12404,plain,
    ( k1_tarski(sK0(X0)) = X0
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5916,c_12395])).

cnf(c_12623,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | k1_tarski(sK0(sK4)) = sK4
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_8330,c_12404])).

cnf(c_12645,plain,
    ( v1_xboole_0(sK4)
    | u1_struct_0(sK2(sK3,sK4)) = sK4
    | k1_tarski(sK0(sK4)) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12623])).

cnf(c_13131,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12623,c_33,c_12645])).

cnf(c_13132,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | k1_tarski(sK0(sK4)) = sK4 ),
    inference(renaming,[status(thm)],[c_13131])).

cnf(c_29,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_5894,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_13136,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v2_tex_2(k6_domain_1(sK4,X0),sK2(sK3,sK4)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2(sK3,sK4))) != iProver_top
    | v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v2_pre_topc(sK2(sK3,sK4)) != iProver_top
    | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13132,c_5894])).

cnf(c_21,plain,
    ( v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_19,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_212,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_19])).

cnf(c_213,plain,
    ( v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_212])).

cnf(c_14,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_16,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_495,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_14,c_16])).

cnf(c_513,plain,
    ( v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_213,c_495])).

cnf(c_5884,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_tdlat_3(X0) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_13137,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v2_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top
    | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13132,c_5884])).

cnf(c_44,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_302,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(prop_impl,[status(thm)],[c_31])).

cnf(c_303,plain,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(renaming,[status(thm)],[c_302])).

cnf(c_1146,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_303])).

cnf(c_1147,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(sK2(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1146])).

cnf(c_1149,plain,
    ( ~ v2_struct_0(sK2(sK3,sK4))
    | v1_zfmisc_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1147,c_37,c_36,c_34,c_33,c_32])).

cnf(c_1151,plain,
    ( v2_struct_0(sK2(sK3,sK4)) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1149])).

cnf(c_27,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_tdlat_3(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1160,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_tdlat_3(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_303])).

cnf(c_1161,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | v1_tdlat_3(sK2(sK3,sK4))
    | ~ v2_pre_topc(sK3)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1160])).

cnf(c_1163,plain,
    ( v1_tdlat_3(sK2(sK3,sK4))
    | v1_zfmisc_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1161,c_37,c_36,c_34,c_33,c_32])).

cnf(c_1165,plain,
    ( v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1163])).

cnf(c_26,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_5897,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_pre_topc(sK2(X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8182,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5891,c_5897])).

cnf(c_8455,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8182,c_38,c_39,c_41,c_42])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_5903,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8461,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | l1_pre_topc(sK2(sK3,sK4)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8455,c_5903])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1410,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X2)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_1411,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_1410])).

cnf(c_5883,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_tdlat_3(X1) != iProver_top
    | v2_tdlat_3(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1411])).

cnf(c_8462,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_tdlat_3(sK2(sK3,sK4)) = iProver_top
    | v2_tdlat_3(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8455,c_5883])).

cnf(c_35,negated_conjecture,
    ( v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_40,plain,
    ( v2_tdlat_3(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_8867,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v2_tdlat_3(sK2(sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8462,c_38,c_40,c_41])).

cnf(c_13391,plain,
    ( v1_zfmisc_1(sK4) = iProver_top
    | k1_tarski(sK0(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13137,c_38,c_40,c_41,c_44,c_1151,c_1165,c_8461,c_8462])).

cnf(c_13392,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_13391])).

cnf(c_13397,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_13392,c_12404])).

cnf(c_13650,plain,
    ( k1_tarski(sK0(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13136,c_42,c_13397])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_5904,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6579,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5891,c_5904])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_5912,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7435,plain,
    ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6579,c_5912])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_228,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_1])).

cnf(c_229,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_228])).

cnf(c_5885,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_7558,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7435,c_5885])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_5902,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7652,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
    | r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7558,c_5902])).

cnf(c_5915,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7559,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7435,c_5915])).

cnf(c_7752,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7652,c_7559])).

cnf(c_7753,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_7752])).

cnf(c_7760,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4))
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5916,c_7753])).

cnf(c_9352,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7760,c_42])).

cnf(c_9355,plain,
    ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9352,c_5894])).

cnf(c_6204,plain,
    ( r2_hidden(sK0(sK4),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6205,plain,
    ( r2_hidden(sK0(sK4),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6204])).

cnf(c_6374,plain,
    ( ~ r1_tarski(sK4,X0)
    | r2_hidden(sK0(sK4),X0)
    | ~ r2_hidden(sK0(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6931,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(X0))
    | r2_hidden(sK0(sK4),u1_struct_0(X0))
    | ~ r2_hidden(sK0(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_6374])).

cnf(c_6933,plain,
    ( r1_tarski(sK4,u1_struct_0(X0)) != iProver_top
    | r2_hidden(sK0(sK4),u1_struct_0(X0)) = iProver_top
    | r2_hidden(sK0(sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6931])).

cnf(c_6935,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(sK4),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(sK4),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6933])).

cnf(c_6274,plain,
    ( m1_subset_1(X0,u1_struct_0(X1))
    | ~ r2_hidden(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_6932,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(X0))
    | ~ r2_hidden(sK0(sK4),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_6274])).

cnf(c_6937,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
    | r2_hidden(sK0(sK4),u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6932])).

cnf(c_6939,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6937])).

cnf(c_9963,plain,
    ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9355,c_38,c_39,c_41,c_42,c_6205,c_6579,c_6935,c_6939])).

cnf(c_13655,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13650,c_9963])).

cnf(c_14720,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_13655,c_8324])).

cnf(c_14770,plain,
    ( v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v2_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top
    | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14720,c_5884])).

cnf(c_5895,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK2(X1,X0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7844,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v2_struct_0(sK2(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5891,c_5895])).

cnf(c_8448,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v2_struct_0(sK2(sK3,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7844,c_38,c_39,c_41,c_42])).

cnf(c_5896,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_tdlat_3(sK2(X1,X0)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7999,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5891,c_5896])).

cnf(c_8214,plain,
    ( v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
    | v2_tex_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7999,c_38,c_39,c_41,c_42])).

cnf(c_8215,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8214])).

cnf(c_30,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_45,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14770,c_13655,c_8867,c_8461,c_8448,c_8215,c_45,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.45/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.00  
% 3.45/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.45/1.00  
% 3.45/1.00  ------  iProver source info
% 3.45/1.00  
% 3.45/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.45/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.45/1.00  git: non_committed_changes: false
% 3.45/1.00  git: last_make_outside_of_git: false
% 3.45/1.00  
% 3.45/1.00  ------ 
% 3.45/1.00  
% 3.45/1.00  ------ Input Options
% 3.45/1.00  
% 3.45/1.00  --out_options                           all
% 3.45/1.00  --tptp_safe_out                         true
% 3.45/1.00  --problem_path                          ""
% 3.45/1.00  --include_path                          ""
% 3.45/1.00  --clausifier                            res/vclausify_rel
% 3.45/1.00  --clausifier_options                    --mode clausify
% 3.45/1.00  --stdin                                 false
% 3.45/1.00  --stats_out                             all
% 3.45/1.00  
% 3.45/1.00  ------ General Options
% 3.45/1.00  
% 3.45/1.00  --fof                                   false
% 3.45/1.00  --time_out_real                         305.
% 3.45/1.00  --time_out_virtual                      -1.
% 3.45/1.00  --symbol_type_check                     false
% 3.45/1.00  --clausify_out                          false
% 3.45/1.00  --sig_cnt_out                           false
% 3.45/1.00  --trig_cnt_out                          false
% 3.45/1.00  --trig_cnt_out_tolerance                1.
% 3.45/1.00  --trig_cnt_out_sk_spl                   false
% 3.45/1.00  --abstr_cl_out                          false
% 3.45/1.00  
% 3.45/1.00  ------ Global Options
% 3.45/1.00  
% 3.45/1.00  --schedule                              default
% 3.45/1.00  --add_important_lit                     false
% 3.45/1.00  --prop_solver_per_cl                    1000
% 3.45/1.00  --min_unsat_core                        false
% 3.45/1.00  --soft_assumptions                      false
% 3.45/1.00  --soft_lemma_size                       3
% 3.45/1.00  --prop_impl_unit_size                   0
% 3.45/1.00  --prop_impl_unit                        []
% 3.45/1.00  --share_sel_clauses                     true
% 3.45/1.00  --reset_solvers                         false
% 3.45/1.00  --bc_imp_inh                            [conj_cone]
% 3.45/1.00  --conj_cone_tolerance                   3.
% 3.45/1.00  --extra_neg_conj                        none
% 3.45/1.00  --large_theory_mode                     true
% 3.45/1.00  --prolific_symb_bound                   200
% 3.45/1.00  --lt_threshold                          2000
% 3.45/1.00  --clause_weak_htbl                      true
% 3.45/1.00  --gc_record_bc_elim                     false
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing Options
% 3.45/1.00  
% 3.45/1.00  --preprocessing_flag                    true
% 3.45/1.00  --time_out_prep_mult                    0.1
% 3.45/1.00  --splitting_mode                        input
% 3.45/1.00  --splitting_grd                         true
% 3.45/1.00  --splitting_cvd                         false
% 3.45/1.00  --splitting_cvd_svl                     false
% 3.45/1.00  --splitting_nvd                         32
% 3.45/1.00  --sub_typing                            true
% 3.45/1.00  --prep_gs_sim                           true
% 3.45/1.00  --prep_unflatten                        true
% 3.45/1.00  --prep_res_sim                          true
% 3.45/1.00  --prep_upred                            true
% 3.45/1.00  --prep_sem_filter                       exhaustive
% 3.45/1.00  --prep_sem_filter_out                   false
% 3.45/1.00  --pred_elim                             true
% 3.45/1.00  --res_sim_input                         true
% 3.45/1.00  --eq_ax_congr_red                       true
% 3.45/1.00  --pure_diseq_elim                       true
% 3.45/1.00  --brand_transform                       false
% 3.45/1.00  --non_eq_to_eq                          false
% 3.45/1.00  --prep_def_merge                        true
% 3.45/1.00  --prep_def_merge_prop_impl              false
% 3.45/1.00  --prep_def_merge_mbd                    true
% 3.45/1.00  --prep_def_merge_tr_red                 false
% 3.45/1.00  --prep_def_merge_tr_cl                  false
% 3.45/1.00  --smt_preprocessing                     true
% 3.45/1.00  --smt_ac_axioms                         fast
% 3.45/1.00  --preprocessed_out                      false
% 3.45/1.00  --preprocessed_stats                    false
% 3.45/1.00  
% 3.45/1.00  ------ Abstraction refinement Options
% 3.45/1.00  
% 3.45/1.00  --abstr_ref                             []
% 3.45/1.00  --abstr_ref_prep                        false
% 3.45/1.00  --abstr_ref_until_sat                   false
% 3.45/1.00  --abstr_ref_sig_restrict                funpre
% 3.45/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/1.00  --abstr_ref_under                       []
% 3.45/1.00  
% 3.45/1.00  ------ SAT Options
% 3.45/1.00  
% 3.45/1.00  --sat_mode                              false
% 3.45/1.00  --sat_fm_restart_options                ""
% 3.45/1.00  --sat_gr_def                            false
% 3.45/1.00  --sat_epr_types                         true
% 3.45/1.00  --sat_non_cyclic_types                  false
% 3.45/1.00  --sat_finite_models                     false
% 3.45/1.00  --sat_fm_lemmas                         false
% 3.45/1.00  --sat_fm_prep                           false
% 3.45/1.00  --sat_fm_uc_incr                        true
% 3.45/1.00  --sat_out_model                         small
% 3.45/1.00  --sat_out_clauses                       false
% 3.45/1.00  
% 3.45/1.00  ------ QBF Options
% 3.45/1.00  
% 3.45/1.00  --qbf_mode                              false
% 3.45/1.00  --qbf_elim_univ                         false
% 3.45/1.00  --qbf_dom_inst                          none
% 3.45/1.00  --qbf_dom_pre_inst                      false
% 3.45/1.00  --qbf_sk_in                             false
% 3.45/1.00  --qbf_pred_elim                         true
% 3.45/1.00  --qbf_split                             512
% 3.45/1.00  
% 3.45/1.00  ------ BMC1 Options
% 3.45/1.00  
% 3.45/1.00  --bmc1_incremental                      false
% 3.45/1.00  --bmc1_axioms                           reachable_all
% 3.45/1.00  --bmc1_min_bound                        0
% 3.45/1.00  --bmc1_max_bound                        -1
% 3.45/1.00  --bmc1_max_bound_default                -1
% 3.45/1.00  --bmc1_symbol_reachability              true
% 3.45/1.00  --bmc1_property_lemmas                  false
% 3.45/1.00  --bmc1_k_induction                      false
% 3.45/1.00  --bmc1_non_equiv_states                 false
% 3.45/1.00  --bmc1_deadlock                         false
% 3.45/1.00  --bmc1_ucm                              false
% 3.45/1.00  --bmc1_add_unsat_core                   none
% 3.45/1.00  --bmc1_unsat_core_children              false
% 3.45/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/1.00  --bmc1_out_stat                         full
% 3.45/1.00  --bmc1_ground_init                      false
% 3.45/1.00  --bmc1_pre_inst_next_state              false
% 3.45/1.00  --bmc1_pre_inst_state                   false
% 3.45/1.00  --bmc1_pre_inst_reach_state             false
% 3.45/1.00  --bmc1_out_unsat_core                   false
% 3.45/1.00  --bmc1_aig_witness_out                  false
% 3.45/1.00  --bmc1_verbose                          false
% 3.45/1.00  --bmc1_dump_clauses_tptp                false
% 3.45/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.45/1.00  --bmc1_dump_file                        -
% 3.45/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.45/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.45/1.00  --bmc1_ucm_extend_mode                  1
% 3.45/1.00  --bmc1_ucm_init_mode                    2
% 3.45/1.00  --bmc1_ucm_cone_mode                    none
% 3.45/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.45/1.00  --bmc1_ucm_relax_model                  4
% 3.45/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.45/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/1.00  --bmc1_ucm_layered_model                none
% 3.45/1.00  --bmc1_ucm_max_lemma_size               10
% 3.45/1.00  
% 3.45/1.00  ------ AIG Options
% 3.45/1.00  
% 3.45/1.00  --aig_mode                              false
% 3.45/1.00  
% 3.45/1.00  ------ Instantiation Options
% 3.45/1.00  
% 3.45/1.00  --instantiation_flag                    true
% 3.45/1.00  --inst_sos_flag                         false
% 3.45/1.00  --inst_sos_phase                        true
% 3.45/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/1.00  --inst_lit_sel_side                     num_symb
% 3.45/1.00  --inst_solver_per_active                1400
% 3.45/1.00  --inst_solver_calls_frac                1.
% 3.45/1.00  --inst_passive_queue_type               priority_queues
% 3.45/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/1.00  --inst_passive_queues_freq              [25;2]
% 3.45/1.00  --inst_dismatching                      true
% 3.45/1.00  --inst_eager_unprocessed_to_passive     true
% 3.45/1.00  --inst_prop_sim_given                   true
% 3.45/1.00  --inst_prop_sim_new                     false
% 3.45/1.00  --inst_subs_new                         false
% 3.45/1.00  --inst_eq_res_simp                      false
% 3.45/1.00  --inst_subs_given                       false
% 3.45/1.00  --inst_orphan_elimination               true
% 3.45/1.00  --inst_learning_loop_flag               true
% 3.45/1.00  --inst_learning_start                   3000
% 3.45/1.00  --inst_learning_factor                  2
% 3.45/1.00  --inst_start_prop_sim_after_learn       3
% 3.45/1.00  --inst_sel_renew                        solver
% 3.45/1.00  --inst_lit_activity_flag                true
% 3.45/1.00  --inst_restr_to_given                   false
% 3.45/1.00  --inst_activity_threshold               500
% 3.45/1.00  --inst_out_proof                        true
% 3.45/1.00  
% 3.45/1.00  ------ Resolution Options
% 3.45/1.00  
% 3.45/1.00  --resolution_flag                       true
% 3.45/1.00  --res_lit_sel                           adaptive
% 3.45/1.00  --res_lit_sel_side                      none
% 3.45/1.00  --res_ordering                          kbo
% 3.45/1.00  --res_to_prop_solver                    active
% 3.45/1.00  --res_prop_simpl_new                    false
% 3.45/1.00  --res_prop_simpl_given                  true
% 3.45/1.00  --res_passive_queue_type                priority_queues
% 3.45/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/1.00  --res_passive_queues_freq               [15;5]
% 3.45/1.00  --res_forward_subs                      full
% 3.45/1.00  --res_backward_subs                     full
% 3.45/1.00  --res_forward_subs_resolution           true
% 3.45/1.00  --res_backward_subs_resolution          true
% 3.45/1.00  --res_orphan_elimination                true
% 3.45/1.00  --res_time_limit                        2.
% 3.45/1.00  --res_out_proof                         true
% 3.45/1.00  
% 3.45/1.00  ------ Superposition Options
% 3.45/1.00  
% 3.45/1.00  --superposition_flag                    true
% 3.45/1.00  --sup_passive_queue_type                priority_queues
% 3.45/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.45/1.00  --demod_completeness_check              fast
% 3.45/1.00  --demod_use_ground                      true
% 3.45/1.00  --sup_to_prop_solver                    passive
% 3.45/1.00  --sup_prop_simpl_new                    true
% 3.45/1.00  --sup_prop_simpl_given                  true
% 3.45/1.00  --sup_fun_splitting                     false
% 3.45/1.00  --sup_smt_interval                      50000
% 3.45/1.00  
% 3.45/1.00  ------ Superposition Simplification Setup
% 3.45/1.00  
% 3.45/1.00  --sup_indices_passive                   []
% 3.45/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_full_bw                           [BwDemod]
% 3.45/1.00  --sup_immed_triv                        [TrivRules]
% 3.45/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_immed_bw_main                     []
% 3.45/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.00  
% 3.45/1.00  ------ Combination Options
% 3.45/1.00  
% 3.45/1.00  --comb_res_mult                         3
% 3.45/1.00  --comb_sup_mult                         2
% 3.45/1.00  --comb_inst_mult                        10
% 3.45/1.00  
% 3.45/1.00  ------ Debug Options
% 3.45/1.00  
% 3.45/1.00  --dbg_backtrace                         false
% 3.45/1.00  --dbg_dump_prop_clauses                 false
% 3.45/1.00  --dbg_dump_prop_clauses_file            -
% 3.45/1.00  --dbg_out_stat                          false
% 3.45/1.00  ------ Parsing...
% 3.45/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.45/1.00  ------ Proving...
% 3.45/1.00  ------ Problem Properties 
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  clauses                                 34
% 3.45/1.00  conjectures                             8
% 3.45/1.00  EPR                                     18
% 3.45/1.00  Horn                                    21
% 3.45/1.00  unary                                   7
% 3.45/1.00  binary                                  11
% 3.45/1.00  lits                                    101
% 3.45/1.00  lits eq                                 3
% 3.45/1.00  fd_pure                                 0
% 3.45/1.00  fd_pseudo                               0
% 3.45/1.00  fd_cond                                 0
% 3.45/1.00  fd_pseudo_cond                          1
% 3.45/1.00  AC symbols                              0
% 3.45/1.00  
% 3.45/1.00  ------ Schedule dynamic 5 is on 
% 3.45/1.00  
% 3.45/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  ------ 
% 3.45/1.00  Current options:
% 3.45/1.00  ------ 
% 3.45/1.00  
% 3.45/1.00  ------ Input Options
% 3.45/1.00  
% 3.45/1.00  --out_options                           all
% 3.45/1.00  --tptp_safe_out                         true
% 3.45/1.00  --problem_path                          ""
% 3.45/1.00  --include_path                          ""
% 3.45/1.00  --clausifier                            res/vclausify_rel
% 3.45/1.00  --clausifier_options                    --mode clausify
% 3.45/1.00  --stdin                                 false
% 3.45/1.00  --stats_out                             all
% 3.45/1.00  
% 3.45/1.00  ------ General Options
% 3.45/1.00  
% 3.45/1.00  --fof                                   false
% 3.45/1.00  --time_out_real                         305.
% 3.45/1.00  --time_out_virtual                      -1.
% 3.45/1.00  --symbol_type_check                     false
% 3.45/1.00  --clausify_out                          false
% 3.45/1.00  --sig_cnt_out                           false
% 3.45/1.00  --trig_cnt_out                          false
% 3.45/1.00  --trig_cnt_out_tolerance                1.
% 3.45/1.00  --trig_cnt_out_sk_spl                   false
% 3.45/1.00  --abstr_cl_out                          false
% 3.45/1.00  
% 3.45/1.00  ------ Global Options
% 3.45/1.00  
% 3.45/1.00  --schedule                              default
% 3.45/1.00  --add_important_lit                     false
% 3.45/1.00  --prop_solver_per_cl                    1000
% 3.45/1.00  --min_unsat_core                        false
% 3.45/1.00  --soft_assumptions                      false
% 3.45/1.00  --soft_lemma_size                       3
% 3.45/1.00  --prop_impl_unit_size                   0
% 3.45/1.00  --prop_impl_unit                        []
% 3.45/1.00  --share_sel_clauses                     true
% 3.45/1.00  --reset_solvers                         false
% 3.45/1.00  --bc_imp_inh                            [conj_cone]
% 3.45/1.00  --conj_cone_tolerance                   3.
% 3.45/1.00  --extra_neg_conj                        none
% 3.45/1.00  --large_theory_mode                     true
% 3.45/1.00  --prolific_symb_bound                   200
% 3.45/1.00  --lt_threshold                          2000
% 3.45/1.00  --clause_weak_htbl                      true
% 3.45/1.00  --gc_record_bc_elim                     false
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing Options
% 3.45/1.00  
% 3.45/1.00  --preprocessing_flag                    true
% 3.45/1.00  --time_out_prep_mult                    0.1
% 3.45/1.00  --splitting_mode                        input
% 3.45/1.00  --splitting_grd                         true
% 3.45/1.00  --splitting_cvd                         false
% 3.45/1.00  --splitting_cvd_svl                     false
% 3.45/1.00  --splitting_nvd                         32
% 3.45/1.00  --sub_typing                            true
% 3.45/1.00  --prep_gs_sim                           true
% 3.45/1.00  --prep_unflatten                        true
% 3.45/1.00  --prep_res_sim                          true
% 3.45/1.00  --prep_upred                            true
% 3.45/1.00  --prep_sem_filter                       exhaustive
% 3.45/1.00  --prep_sem_filter_out                   false
% 3.45/1.00  --pred_elim                             true
% 3.45/1.00  --res_sim_input                         true
% 3.45/1.00  --eq_ax_congr_red                       true
% 3.45/1.00  --pure_diseq_elim                       true
% 3.45/1.00  --brand_transform                       false
% 3.45/1.00  --non_eq_to_eq                          false
% 3.45/1.00  --prep_def_merge                        true
% 3.45/1.00  --prep_def_merge_prop_impl              false
% 3.45/1.00  --prep_def_merge_mbd                    true
% 3.45/1.00  --prep_def_merge_tr_red                 false
% 3.45/1.00  --prep_def_merge_tr_cl                  false
% 3.45/1.00  --smt_preprocessing                     true
% 3.45/1.00  --smt_ac_axioms                         fast
% 3.45/1.00  --preprocessed_out                      false
% 3.45/1.00  --preprocessed_stats                    false
% 3.45/1.00  
% 3.45/1.00  ------ Abstraction refinement Options
% 3.45/1.00  
% 3.45/1.00  --abstr_ref                             []
% 3.45/1.00  --abstr_ref_prep                        false
% 3.45/1.00  --abstr_ref_until_sat                   false
% 3.45/1.00  --abstr_ref_sig_restrict                funpre
% 3.45/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/1.00  --abstr_ref_under                       []
% 3.45/1.00  
% 3.45/1.00  ------ SAT Options
% 3.45/1.00  
% 3.45/1.00  --sat_mode                              false
% 3.45/1.00  --sat_fm_restart_options                ""
% 3.45/1.00  --sat_gr_def                            false
% 3.45/1.00  --sat_epr_types                         true
% 3.45/1.00  --sat_non_cyclic_types                  false
% 3.45/1.00  --sat_finite_models                     false
% 3.45/1.00  --sat_fm_lemmas                         false
% 3.45/1.00  --sat_fm_prep                           false
% 3.45/1.00  --sat_fm_uc_incr                        true
% 3.45/1.00  --sat_out_model                         small
% 3.45/1.00  --sat_out_clauses                       false
% 3.45/1.00  
% 3.45/1.00  ------ QBF Options
% 3.45/1.00  
% 3.45/1.00  --qbf_mode                              false
% 3.45/1.00  --qbf_elim_univ                         false
% 3.45/1.00  --qbf_dom_inst                          none
% 3.45/1.00  --qbf_dom_pre_inst                      false
% 3.45/1.00  --qbf_sk_in                             false
% 3.45/1.00  --qbf_pred_elim                         true
% 3.45/1.00  --qbf_split                             512
% 3.45/1.00  
% 3.45/1.00  ------ BMC1 Options
% 3.45/1.00  
% 3.45/1.00  --bmc1_incremental                      false
% 3.45/1.00  --bmc1_axioms                           reachable_all
% 3.45/1.00  --bmc1_min_bound                        0
% 3.45/1.00  --bmc1_max_bound                        -1
% 3.45/1.00  --bmc1_max_bound_default                -1
% 3.45/1.00  --bmc1_symbol_reachability              true
% 3.45/1.00  --bmc1_property_lemmas                  false
% 3.45/1.00  --bmc1_k_induction                      false
% 3.45/1.00  --bmc1_non_equiv_states                 false
% 3.45/1.00  --bmc1_deadlock                         false
% 3.45/1.00  --bmc1_ucm                              false
% 3.45/1.00  --bmc1_add_unsat_core                   none
% 3.45/1.00  --bmc1_unsat_core_children              false
% 3.45/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/1.00  --bmc1_out_stat                         full
% 3.45/1.00  --bmc1_ground_init                      false
% 3.45/1.00  --bmc1_pre_inst_next_state              false
% 3.45/1.00  --bmc1_pre_inst_state                   false
% 3.45/1.00  --bmc1_pre_inst_reach_state             false
% 3.45/1.00  --bmc1_out_unsat_core                   false
% 3.45/1.00  --bmc1_aig_witness_out                  false
% 3.45/1.00  --bmc1_verbose                          false
% 3.45/1.00  --bmc1_dump_clauses_tptp                false
% 3.45/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.45/1.00  --bmc1_dump_file                        -
% 3.45/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.45/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.45/1.00  --bmc1_ucm_extend_mode                  1
% 3.45/1.00  --bmc1_ucm_init_mode                    2
% 3.45/1.00  --bmc1_ucm_cone_mode                    none
% 3.45/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.45/1.00  --bmc1_ucm_relax_model                  4
% 3.45/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.45/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/1.00  --bmc1_ucm_layered_model                none
% 3.45/1.00  --bmc1_ucm_max_lemma_size               10
% 3.45/1.00  
% 3.45/1.00  ------ AIG Options
% 3.45/1.00  
% 3.45/1.00  --aig_mode                              false
% 3.45/1.00  
% 3.45/1.00  ------ Instantiation Options
% 3.45/1.00  
% 3.45/1.00  --instantiation_flag                    true
% 3.45/1.00  --inst_sos_flag                         false
% 3.45/1.00  --inst_sos_phase                        true
% 3.45/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/1.00  --inst_lit_sel_side                     none
% 3.45/1.00  --inst_solver_per_active                1400
% 3.45/1.00  --inst_solver_calls_frac                1.
% 3.45/1.00  --inst_passive_queue_type               priority_queues
% 3.45/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/1.00  --inst_passive_queues_freq              [25;2]
% 3.45/1.00  --inst_dismatching                      true
% 3.45/1.00  --inst_eager_unprocessed_to_passive     true
% 3.45/1.00  --inst_prop_sim_given                   true
% 3.45/1.00  --inst_prop_sim_new                     false
% 3.45/1.00  --inst_subs_new                         false
% 3.45/1.00  --inst_eq_res_simp                      false
% 3.45/1.00  --inst_subs_given                       false
% 3.45/1.00  --inst_orphan_elimination               true
% 3.45/1.00  --inst_learning_loop_flag               true
% 3.45/1.00  --inst_learning_start                   3000
% 3.45/1.00  --inst_learning_factor                  2
% 3.45/1.00  --inst_start_prop_sim_after_learn       3
% 3.45/1.00  --inst_sel_renew                        solver
% 3.45/1.00  --inst_lit_activity_flag                true
% 3.45/1.00  --inst_restr_to_given                   false
% 3.45/1.00  --inst_activity_threshold               500
% 3.45/1.00  --inst_out_proof                        true
% 3.45/1.00  
% 3.45/1.00  ------ Resolution Options
% 3.45/1.00  
% 3.45/1.00  --resolution_flag                       false
% 3.45/1.00  --res_lit_sel                           adaptive
% 3.45/1.00  --res_lit_sel_side                      none
% 3.45/1.00  --res_ordering                          kbo
% 3.45/1.00  --res_to_prop_solver                    active
% 3.45/1.00  --res_prop_simpl_new                    false
% 3.45/1.00  --res_prop_simpl_given                  true
% 3.45/1.00  --res_passive_queue_type                priority_queues
% 3.45/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/1.00  --res_passive_queues_freq               [15;5]
% 3.45/1.00  --res_forward_subs                      full
% 3.45/1.00  --res_backward_subs                     full
% 3.45/1.00  --res_forward_subs_resolution           true
% 3.45/1.00  --res_backward_subs_resolution          true
% 3.45/1.00  --res_orphan_elimination                true
% 3.45/1.00  --res_time_limit                        2.
% 3.45/1.00  --res_out_proof                         true
% 3.45/1.00  
% 3.45/1.00  ------ Superposition Options
% 3.45/1.00  
% 3.45/1.00  --superposition_flag                    true
% 3.45/1.00  --sup_passive_queue_type                priority_queues
% 3.45/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.45/1.00  --demod_completeness_check              fast
% 3.45/1.00  --demod_use_ground                      true
% 3.45/1.00  --sup_to_prop_solver                    passive
% 3.45/1.00  --sup_prop_simpl_new                    true
% 3.45/1.00  --sup_prop_simpl_given                  true
% 3.45/1.00  --sup_fun_splitting                     false
% 3.45/1.00  --sup_smt_interval                      50000
% 3.45/1.00  
% 3.45/1.00  ------ Superposition Simplification Setup
% 3.45/1.00  
% 3.45/1.00  --sup_indices_passive                   []
% 3.45/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_full_bw                           [BwDemod]
% 3.45/1.00  --sup_immed_triv                        [TrivRules]
% 3.45/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_immed_bw_main                     []
% 3.45/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.00  
% 3.45/1.00  ------ Combination Options
% 3.45/1.00  
% 3.45/1.00  --comb_res_mult                         3
% 3.45/1.00  --comb_sup_mult                         2
% 3.45/1.00  --comb_inst_mult                        10
% 3.45/1.00  
% 3.45/1.00  ------ Debug Options
% 3.45/1.00  
% 3.45/1.00  --dbg_backtrace                         false
% 3.45/1.00  --dbg_dump_prop_clauses                 false
% 3.45/1.00  --dbg_dump_prop_clauses_file            -
% 3.45/1.00  --dbg_out_stat                          false
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  ------ Proving...
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  % SZS status Theorem for theBenchmark.p
% 3.45/1.00  
% 3.45/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.45/1.00  
% 3.45/1.00  fof(f18,conjecture,(
% 3.45/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f19,negated_conjecture,(
% 3.45/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.45/1.00    inference(negated_conjecture,[],[f18])).
% 3.45/1.00  
% 3.45/1.00  fof(f43,plain,(
% 3.45/1.00    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f19])).
% 3.45/1.00  
% 3.45/1.00  fof(f44,plain,(
% 3.45/1.00    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.45/1.00    inference(flattening,[],[f43])).
% 3.45/1.00  
% 3.45/1.00  fof(f58,plain,(
% 3.45/1.00    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.45/1.00    inference(nnf_transformation,[],[f44])).
% 3.45/1.00  
% 3.45/1.00  fof(f59,plain,(
% 3.45/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.45/1.00    inference(flattening,[],[f58])).
% 3.45/1.00  
% 3.45/1.00  fof(f61,plain,(
% 3.45/1.00    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,X0)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK4))) )),
% 3.45/1.00    introduced(choice_axiom,[])).
% 3.45/1.00  
% 3.45/1.00  fof(f60,plain,(
% 3.45/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.45/1.00    introduced(choice_axiom,[])).
% 3.45/1.00  
% 3.45/1.00  fof(f62,plain,(
% 3.45/1.00    ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.45/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f59,f61,f60])).
% 3.45/1.00  
% 3.45/1.00  fof(f99,plain,(
% 3.45/1.00    v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)),
% 3.45/1.00    inference(cnf_transformation,[],[f62])).
% 3.45/1.00  
% 3.45/1.00  fof(f98,plain,(
% 3.45/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.45/1.00    inference(cnf_transformation,[],[f62])).
% 3.45/1.00  
% 3.45/1.00  fof(f16,axiom,(
% 3.45/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f20,plain,(
% 3.45/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.45/1.00    inference(pure_predicate_removal,[],[f16])).
% 3.45/1.00  
% 3.45/1.00  fof(f39,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f20])).
% 3.45/1.00  
% 3.45/1.00  fof(f40,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/1.00    inference(flattening,[],[f39])).
% 3.45/1.00  
% 3.45/1.00  fof(f56,plain,(
% 3.45/1.00    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 3.45/1.00    introduced(choice_axiom,[])).
% 3.45/1.00  
% 3.45/1.00  fof(f57,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f56])).
% 3.45/1.00  
% 3.45/1.00  fof(f91,plain,(
% 3.45/1.00    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f57])).
% 3.45/1.00  
% 3.45/1.00  fof(f93,plain,(
% 3.45/1.00    ~v2_struct_0(sK3)),
% 3.45/1.00    inference(cnf_transformation,[],[f62])).
% 3.45/1.00  
% 3.45/1.00  fof(f94,plain,(
% 3.45/1.00    v2_pre_topc(sK3)),
% 3.45/1.00    inference(cnf_transformation,[],[f62])).
% 3.45/1.00  
% 3.45/1.00  fof(f96,plain,(
% 3.45/1.00    l1_pre_topc(sK3)),
% 3.45/1.00    inference(cnf_transformation,[],[f62])).
% 3.45/1.00  
% 3.45/1.00  fof(f97,plain,(
% 3.45/1.00    ~v1_xboole_0(sK4)),
% 3.45/1.00    inference(cnf_transformation,[],[f62])).
% 3.45/1.00  
% 3.45/1.00  fof(f1,axiom,(
% 3.45/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f45,plain,(
% 3.45/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.45/1.00    inference(nnf_transformation,[],[f1])).
% 3.45/1.00  
% 3.45/1.00  fof(f46,plain,(
% 3.45/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.45/1.00    inference(rectify,[],[f45])).
% 3.45/1.00  
% 3.45/1.00  fof(f47,plain,(
% 3.45/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.45/1.00    introduced(choice_axiom,[])).
% 3.45/1.00  
% 3.45/1.00  fof(f48,plain,(
% 3.45/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.45/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).
% 3.45/1.00  
% 3.45/1.00  fof(f64,plain,(
% 3.45/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f48])).
% 3.45/1.00  
% 3.45/1.00  fof(f4,axiom,(
% 3.45/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f53,plain,(
% 3.45/1.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.45/1.00    inference(nnf_transformation,[],[f4])).
% 3.45/1.00  
% 3.45/1.00  fof(f70,plain,(
% 3.45/1.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f53])).
% 3.45/1.00  
% 3.45/1.00  fof(f15,axiom,(
% 3.45/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f37,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 3.45/1.00    inference(ennf_transformation,[],[f15])).
% 3.45/1.00  
% 3.45/1.00  fof(f38,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.45/1.00    inference(flattening,[],[f37])).
% 3.45/1.00  
% 3.45/1.00  fof(f87,plain,(
% 3.45/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f38])).
% 3.45/1.00  
% 3.45/1.00  fof(f3,axiom,(
% 3.45/1.00    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f68,plain,(
% 3.45/1.00    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f3])).
% 3.45/1.00  
% 3.45/1.00  fof(f63,plain,(
% 3.45/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f48])).
% 3.45/1.00  
% 3.45/1.00  fof(f17,axiom,(
% 3.45/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f41,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f17])).
% 3.45/1.00  
% 3.45/1.00  fof(f42,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/1.00    inference(flattening,[],[f41])).
% 3.45/1.00  
% 3.45/1.00  fof(f92,plain,(
% 3.45/1.00    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f42])).
% 3.45/1.00  
% 3.45/1.00  fof(f13,axiom,(
% 3.45/1.00    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f33,plain,(
% 3.45/1.00    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(ennf_transformation,[],[f13])).
% 3.45/1.00  
% 3.45/1.00  fof(f34,plain,(
% 3.45/1.00    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(flattening,[],[f33])).
% 3.45/1.00  
% 3.45/1.00  fof(f84,plain,(
% 3.45/1.00    ( ! [X0] : (v7_struct_0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f34])).
% 3.45/1.00  
% 3.45/1.00  fof(f12,axiom,(
% 3.45/1.00    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f31,plain,(
% 3.45/1.00    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(ennf_transformation,[],[f12])).
% 3.45/1.00  
% 3.45/1.00  fof(f32,plain,(
% 3.45/1.00    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(flattening,[],[f31])).
% 3.45/1.00  
% 3.45/1.00  fof(f82,plain,(
% 3.45/1.00    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f32])).
% 3.45/1.00  
% 3.45/1.00  fof(f7,axiom,(
% 3.45/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f23,plain,(
% 3.45/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(ennf_transformation,[],[f7])).
% 3.45/1.00  
% 3.45/1.00  fof(f77,plain,(
% 3.45/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f23])).
% 3.45/1.00  
% 3.45/1.00  fof(f9,axiom,(
% 3.45/1.00    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f25,plain,(
% 3.45/1.00    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f9])).
% 3.45/1.00  
% 3.45/1.00  fof(f26,plain,(
% 3.45/1.00    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 3.45/1.00    inference(flattening,[],[f25])).
% 3.45/1.00  
% 3.45/1.00  fof(f79,plain,(
% 3.45/1.00    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f26])).
% 3.45/1.00  
% 3.45/1.00  fof(f88,plain,(
% 3.45/1.00    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f57])).
% 3.45/1.00  
% 3.45/1.00  fof(f89,plain,(
% 3.45/1.00    ( ! [X0,X1] : (v1_tdlat_3(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f57])).
% 3.45/1.00  
% 3.45/1.00  fof(f90,plain,(
% 3.45/1.00    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f57])).
% 3.45/1.00  
% 3.45/1.00  fof(f8,axiom,(
% 3.45/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f24,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(ennf_transformation,[],[f8])).
% 3.45/1.00  
% 3.45/1.00  fof(f78,plain,(
% 3.45/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f24])).
% 3.45/1.00  
% 3.45/1.00  fof(f14,axiom,(
% 3.45/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f35,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f14])).
% 3.45/1.00  
% 3.45/1.00  fof(f36,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/1.00    inference(flattening,[],[f35])).
% 3.45/1.00  
% 3.45/1.00  fof(f86,plain,(
% 3.45/1.00    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f36])).
% 3.45/1.00  
% 3.45/1.00  fof(f95,plain,(
% 3.45/1.00    v2_tdlat_3(sK3)),
% 3.45/1.00    inference(cnf_transformation,[],[f62])).
% 3.45/1.00  
% 3.45/1.00  fof(f6,axiom,(
% 3.45/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f55,plain,(
% 3.45/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.45/1.00    inference(nnf_transformation,[],[f6])).
% 3.45/1.00  
% 3.45/1.00  fof(f75,plain,(
% 3.45/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f55])).
% 3.45/1.00  
% 3.45/1.00  fof(f2,axiom,(
% 3.45/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f21,plain,(
% 3.45/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f2])).
% 3.45/1.00  
% 3.45/1.00  fof(f49,plain,(
% 3.45/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.45/1.00    inference(nnf_transformation,[],[f21])).
% 3.45/1.00  
% 3.45/1.00  fof(f50,plain,(
% 3.45/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.45/1.00    inference(rectify,[],[f49])).
% 3.45/1.00  
% 3.45/1.00  fof(f51,plain,(
% 3.45/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.45/1.00    introduced(choice_axiom,[])).
% 3.45/1.00  
% 3.45/1.00  fof(f52,plain,(
% 3.45/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.45/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f51])).
% 3.45/1.00  
% 3.45/1.00  fof(f65,plain,(
% 3.45/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f52])).
% 3.45/1.00  
% 3.45/1.00  fof(f5,axiom,(
% 3.45/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f22,plain,(
% 3.45/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f5])).
% 3.45/1.00  
% 3.45/1.00  fof(f54,plain,(
% 3.45/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.45/1.00    inference(nnf_transformation,[],[f22])).
% 3.45/1.00  
% 3.45/1.00  fof(f72,plain,(
% 3.45/1.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f54])).
% 3.45/1.00  
% 3.45/1.00  fof(f10,axiom,(
% 3.45/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f27,plain,(
% 3.45/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f10])).
% 3.45/1.00  
% 3.45/1.00  fof(f28,plain,(
% 3.45/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.45/1.00    inference(flattening,[],[f27])).
% 3.45/1.00  
% 3.45/1.00  fof(f80,plain,(
% 3.45/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f28])).
% 3.45/1.00  
% 3.45/1.00  fof(f100,plain,(
% 3.45/1.00    ~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)),
% 3.45/1.00    inference(cnf_transformation,[],[f62])).
% 3.45/1.00  
% 3.45/1.00  cnf(c_31,negated_conjecture,
% 3.45/1.00      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 3.45/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5892,plain,
% 3.45/1.00      ( v2_tex_2(sK4,sK3) = iProver_top
% 3.45/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_32,negated_conjecture,
% 3.45/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.45/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5891,plain,
% 3.45/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_25,plain,
% 3.45/1.00      ( ~ v2_tex_2(X0,X1)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | v1_xboole_0(X0)
% 3.45/1.00      | u1_struct_0(sK2(X1,X0)) = X0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5898,plain,
% 3.45/1.00      ( u1_struct_0(sK2(X0,X1)) = X1
% 3.45/1.00      | v2_tex_2(X1,X0) != iProver_top
% 3.45/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.45/1.00      | v2_struct_0(X0) = iProver_top
% 3.45/1.00      | v2_pre_topc(X0) != iProver_top
% 3.45/1.00      | l1_pre_topc(X0) != iProver_top
% 3.45/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8040,plain,
% 3.45/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.45/1.00      | v2_tex_2(sK4,sK3) != iProver_top
% 3.45/1.00      | v2_struct_0(sK3) = iProver_top
% 3.45/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.45/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.45/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_5891,c_5898]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_37,negated_conjecture,
% 3.45/1.00      ( ~ v2_struct_0(sK3) ),
% 3.45/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_38,plain,
% 3.45/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_36,negated_conjecture,
% 3.45/1.00      ( v2_pre_topc(sK3) ),
% 3.45/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_39,plain,
% 3.45/1.00      ( v2_pre_topc(sK3) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_34,negated_conjecture,
% 3.45/1.00      ( l1_pre_topc(sK3) ),
% 3.45/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_41,plain,
% 3.45/1.00      ( l1_pre_topc(sK3) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_33,negated_conjecture,
% 3.45/1.00      ( ~ v1_xboole_0(sK4) ),
% 3.45/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_42,plain,
% 3.45/1.00      ( v1_xboole_0(sK4) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8324,plain,
% 3.45/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.45/1.00      | v2_tex_2(sK4,sK3) != iProver_top ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_8040,c_38,c_39,c_41,c_42]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8330,plain,
% 3.45/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.45/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_5892,c_8324]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_0,plain,
% 3.45/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5916,plain,
% 3.45/1.00      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.45/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_6,plain,
% 3.45/1.00      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5910,plain,
% 3.45/1.00      ( r1_tarski(k1_tarski(X0),X1) = iProver_top
% 3.45/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_24,plain,
% 3.45/1.00      ( ~ r1_tarski(X0,X1)
% 3.45/1.00      | ~ v1_zfmisc_1(X1)
% 3.45/1.00      | v1_xboole_0(X0)
% 3.45/1.00      | v1_xboole_0(X1)
% 3.45/1.00      | X1 = X0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5899,plain,
% 3.45/1.00      ( X0 = X1
% 3.45/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.45/1.00      | v1_zfmisc_1(X0) != iProver_top
% 3.45/1.00      | v1_xboole_0(X1) = iProver_top
% 3.45/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_7882,plain,
% 3.45/1.00      ( k1_tarski(X0) = X1
% 3.45/1.00      | r2_hidden(X0,X1) != iProver_top
% 3.45/1.00      | v1_zfmisc_1(X1) != iProver_top
% 3.45/1.00      | v1_xboole_0(X1) = iProver_top
% 3.45/1.00      | v1_xboole_0(k1_tarski(X0)) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_5910,c_5899]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5,plain,
% 3.45/1.00      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 3.45/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_104,plain,
% 3.45/1.00      ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1,plain,
% 3.45/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_114,plain,
% 3.45/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.45/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_12395,plain,
% 3.45/1.00      ( k1_tarski(X0) = X1
% 3.45/1.00      | r2_hidden(X0,X1) != iProver_top
% 3.45/1.00      | v1_zfmisc_1(X1) != iProver_top ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_7882,c_104,c_114]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_12404,plain,
% 3.45/1.00      ( k1_tarski(sK0(X0)) = X0
% 3.45/1.00      | v1_zfmisc_1(X0) != iProver_top
% 3.45/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_5916,c_12395]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_12623,plain,
% 3.45/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.45/1.00      | k1_tarski(sK0(sK4)) = sK4
% 3.45/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_8330,c_12404]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_12645,plain,
% 3.45/1.00      ( v1_xboole_0(sK4)
% 3.45/1.00      | u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.45/1.00      | k1_tarski(sK0(sK4)) = sK4 ),
% 3.45/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_12623]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_13131,plain,
% 3.45/1.00      ( k1_tarski(sK0(sK4)) = sK4 | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_12623,c_33,c_12645]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_13132,plain,
% 3.45/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4 | k1_tarski(sK0(sK4)) = sK4 ),
% 3.45/1.00      inference(renaming,[status(thm)],[c_13131]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_29,plain,
% 3.45/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.45/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.45/1.00      | v2_struct_0(X0)
% 3.45/1.00      | ~ v2_pre_topc(X0)
% 3.45/1.00      | ~ l1_pre_topc(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5894,plain,
% 3.45/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) = iProver_top
% 3.45/1.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.45/1.00      | v2_struct_0(X0) = iProver_top
% 3.45/1.00      | v2_pre_topc(X0) != iProver_top
% 3.45/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_13136,plain,
% 3.45/1.00      ( k1_tarski(sK0(sK4)) = sK4
% 3.45/1.00      | v2_tex_2(k6_domain_1(sK4,X0),sK2(sK3,sK4)) = iProver_top
% 3.45/1.00      | m1_subset_1(X0,u1_struct_0(sK2(sK3,sK4))) != iProver_top
% 3.45/1.00      | v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 3.45/1.00      | v2_pre_topc(sK2(sK3,sK4)) != iProver_top
% 3.45/1.00      | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_13132,c_5894]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_21,plain,
% 3.45/1.00      ( v2_struct_0(X0)
% 3.45/1.00      | ~ v2_tdlat_3(X0)
% 3.45/1.00      | ~ v1_tdlat_3(X0)
% 3.45/1.00      | ~ v2_pre_topc(X0)
% 3.45/1.00      | v7_struct_0(X0)
% 3.45/1.00      | ~ l1_pre_topc(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_19,plain,
% 3.45/1.00      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_212,plain,
% 3.45/1.00      ( ~ v1_tdlat_3(X0)
% 3.45/1.00      | ~ v2_tdlat_3(X0)
% 3.45/1.00      | v2_struct_0(X0)
% 3.45/1.00      | v7_struct_0(X0)
% 3.45/1.00      | ~ l1_pre_topc(X0) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_21,c_19]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_213,plain,
% 3.45/1.00      ( v2_struct_0(X0)
% 3.45/1.00      | ~ v2_tdlat_3(X0)
% 3.45/1.00      | ~ v1_tdlat_3(X0)
% 3.45/1.00      | v7_struct_0(X0)
% 3.45/1.00      | ~ l1_pre_topc(X0) ),
% 3.45/1.00      inference(renaming,[status(thm)],[c_212]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_14,plain,
% 3.45/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_16,plain,
% 3.45/1.00      ( ~ v7_struct_0(X0)
% 3.45/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.45/1.00      | ~ l1_struct_0(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_495,plain,
% 3.45/1.00      ( ~ v7_struct_0(X0)
% 3.45/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.45/1.00      | ~ l1_pre_topc(X0) ),
% 3.45/1.00      inference(resolution,[status(thm)],[c_14,c_16]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_513,plain,
% 3.45/1.00      ( v2_struct_0(X0)
% 3.45/1.00      | ~ v2_tdlat_3(X0)
% 3.45/1.00      | ~ v1_tdlat_3(X0)
% 3.45/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.45/1.00      | ~ l1_pre_topc(X0) ),
% 3.45/1.00      inference(resolution,[status(thm)],[c_213,c_495]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5884,plain,
% 3.45/1.00      ( v2_struct_0(X0) = iProver_top
% 3.45/1.00      | v2_tdlat_3(X0) != iProver_top
% 3.45/1.00      | v1_tdlat_3(X0) != iProver_top
% 3.45/1.00      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
% 3.45/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_13137,plain,
% 3.45/1.00      ( k1_tarski(sK0(sK4)) = sK4
% 3.45/1.00      | v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 3.45/1.00      | v2_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 3.45/1.00      | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 3.45/1.00      | v1_zfmisc_1(sK4) = iProver_top
% 3.45/1.00      | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_13132,c_5884]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_44,plain,
% 3.45/1.00      ( v2_tex_2(sK4,sK3) = iProver_top
% 3.45/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_28,plain,
% 3.45/1.00      ( ~ v2_tex_2(X0,X1)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | ~ v2_struct_0(sK2(X1,X0))
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | v1_xboole_0(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_302,plain,
% 3.45/1.00      ( v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3) ),
% 3.45/1.00      inference(prop_impl,[status(thm)],[c_31]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_303,plain,
% 3.45/1.00      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 3.45/1.00      inference(renaming,[status(thm)],[c_302]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1146,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | ~ v2_struct_0(sK2(X1,X0))
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | v1_zfmisc_1(sK4)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | v1_xboole_0(X0)
% 3.45/1.00      | sK3 != X1
% 3.45/1.00      | sK4 != X0 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_303]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1147,plain,
% 3.45/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.45/1.00      | ~ v2_struct_0(sK2(sK3,sK4))
% 3.45/1.00      | v2_struct_0(sK3)
% 3.45/1.00      | ~ v2_pre_topc(sK3)
% 3.45/1.00      | v1_zfmisc_1(sK4)
% 3.45/1.00      | ~ l1_pre_topc(sK3)
% 3.45/1.00      | v1_xboole_0(sK4) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_1146]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1149,plain,
% 3.45/1.00      ( ~ v2_struct_0(sK2(sK3,sK4)) | v1_zfmisc_1(sK4) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_1147,c_37,c_36,c_34,c_33,c_32]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1151,plain,
% 3.45/1.00      ( v2_struct_0(sK2(sK3,sK4)) != iProver_top
% 3.45/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1149]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_27,plain,
% 3.45/1.00      ( ~ v2_tex_2(X0,X1)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | v1_tdlat_3(sK2(X1,X0))
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | v1_xboole_0(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1160,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | v1_tdlat_3(sK2(X1,X0))
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | v1_zfmisc_1(sK4)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | v1_xboole_0(X0)
% 3.45/1.00      | sK3 != X1
% 3.45/1.00      | sK4 != X0 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_303]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1161,plain,
% 3.45/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.45/1.00      | v2_struct_0(sK3)
% 3.45/1.00      | v1_tdlat_3(sK2(sK3,sK4))
% 3.45/1.00      | ~ v2_pre_topc(sK3)
% 3.45/1.00      | v1_zfmisc_1(sK4)
% 3.45/1.00      | ~ l1_pre_topc(sK3)
% 3.45/1.00      | v1_xboole_0(sK4) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_1160]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1163,plain,
% 3.45/1.00      ( v1_tdlat_3(sK2(sK3,sK4)) | v1_zfmisc_1(sK4) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_1161,c_37,c_36,c_34,c_33,c_32]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1165,plain,
% 3.45/1.00      ( v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
% 3.45/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1163]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_26,plain,
% 3.45/1.00      ( ~ v2_tex_2(X0,X1)
% 3.45/1.00      | m1_pre_topc(sK2(X1,X0),X1)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | v1_xboole_0(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5897,plain,
% 3.45/1.00      ( v2_tex_2(X0,X1) != iProver_top
% 3.45/1.00      | m1_pre_topc(sK2(X1,X0),X1) = iProver_top
% 3.45/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.45/1.00      | v2_struct_0(X1) = iProver_top
% 3.45/1.00      | v2_pre_topc(X1) != iProver_top
% 3.45/1.00      | l1_pre_topc(X1) != iProver_top
% 3.45/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8182,plain,
% 3.45/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.45/1.00      | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
% 3.45/1.00      | v2_struct_0(sK3) = iProver_top
% 3.45/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.45/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.45/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_5891,c_5897]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8455,plain,
% 3.45/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.45/1.00      | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_8182,c_38,c_39,c_41,c_42]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_15,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5903,plain,
% 3.45/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.45/1.00      | l1_pre_topc(X1) != iProver_top
% 3.45/1.00      | l1_pre_topc(X0) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8461,plain,
% 3.45/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.45/1.00      | l1_pre_topc(sK2(sK3,sK4)) = iProver_top
% 3.45/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_8455,c_5903]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_23,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | ~ v2_tdlat_3(X1)
% 3.45/1.00      | v2_tdlat_3(X0)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1410,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | ~ v2_tdlat_3(X2)
% 3.45/1.00      | ~ v2_tdlat_3(X1)
% 3.45/1.00      | v2_tdlat_3(X0)
% 3.45/1.00      | ~ l1_pre_topc(X2)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | X1 != X2 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1411,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | ~ v2_tdlat_3(X1)
% 3.45/1.00      | v2_tdlat_3(X0)
% 3.45/1.00      | ~ l1_pre_topc(X1) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_1410]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5883,plain,
% 3.45/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.45/1.00      | v2_struct_0(X1) = iProver_top
% 3.45/1.00      | v2_tdlat_3(X1) != iProver_top
% 3.45/1.00      | v2_tdlat_3(X0) = iProver_top
% 3.45/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1411]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8462,plain,
% 3.45/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.45/1.00      | v2_struct_0(sK3) = iProver_top
% 3.45/1.00      | v2_tdlat_3(sK2(sK3,sK4)) = iProver_top
% 3.45/1.00      | v2_tdlat_3(sK3) != iProver_top
% 3.45/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_8455,c_5883]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_35,negated_conjecture,
% 3.45/1.00      ( v2_tdlat_3(sK3) ),
% 3.45/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_40,plain,
% 3.45/1.00      ( v2_tdlat_3(sK3) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8867,plain,
% 3.45/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.45/1.00      | v2_tdlat_3(sK2(sK3,sK4)) = iProver_top ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_8462,c_38,c_40,c_41]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_13391,plain,
% 3.45/1.00      ( v1_zfmisc_1(sK4) = iProver_top | k1_tarski(sK0(sK4)) = sK4 ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_13137,c_38,c_40,c_41,c_44,c_1151,c_1165,c_8461,c_8462]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_13392,plain,
% 3.45/1.01      ( k1_tarski(sK0(sK4)) = sK4 | v1_zfmisc_1(sK4) = iProver_top ),
% 3.45/1.01      inference(renaming,[status(thm)],[c_13391]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_13397,plain,
% 3.45/1.01      ( k1_tarski(sK0(sK4)) = sK4 | v1_xboole_0(sK4) = iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_13392,c_12404]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_13650,plain,
% 3.45/1.01      ( k1_tarski(sK0(sK4)) = sK4 ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_13136,c_42,c_13397]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_13,plain,
% 3.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.45/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_5904,plain,
% 3.45/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.45/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6579,plain,
% 3.45/1.01      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_5891,c_5904]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_4,plain,
% 3.45/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.45/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_5912,plain,
% 3.45/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.45/1.01      | r2_hidden(X2,X0) != iProver_top
% 3.45/1.01      | r2_hidden(X2,X1) = iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7435,plain,
% 3.45/1.01      ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
% 3.45/1.01      | r2_hidden(X0,sK4) != iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_6579,c_5912]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_10,plain,
% 3.45/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.45/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_228,plain,
% 3.45/1.01      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_10,c_1]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_229,plain,
% 3.45/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.45/1.01      inference(renaming,[status(thm)],[c_228]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_5885,plain,
% 3.45/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 3.45/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7558,plain,
% 3.45/1.01      ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
% 3.45/1.01      | r2_hidden(X0,sK4) != iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_7435,c_5885]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_17,plain,
% 3.45/1.01      ( ~ m1_subset_1(X0,X1)
% 3.45/1.01      | v1_xboole_0(X1)
% 3.45/1.01      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.45/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_5902,plain,
% 3.45/1.01      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 3.45/1.01      | m1_subset_1(X1,X0) != iProver_top
% 3.45/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7652,plain,
% 3.45/1.01      ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
% 3.45/1.01      | r2_hidden(X0,sK4) != iProver_top
% 3.45/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_7558,c_5902]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_5915,plain,
% 3.45/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.45/1.01      | v1_xboole_0(X1) != iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7559,plain,
% 3.45/1.01      ( r2_hidden(X0,sK4) != iProver_top
% 3.45/1.01      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_7435,c_5915]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7752,plain,
% 3.45/1.01      ( r2_hidden(X0,sK4) != iProver_top
% 3.45/1.01      | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_7652,c_7559]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7753,plain,
% 3.45/1.01      ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
% 3.45/1.01      | r2_hidden(X0,sK4) != iProver_top ),
% 3.45/1.01      inference(renaming,[status(thm)],[c_7752]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7760,plain,
% 3.45/1.01      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4))
% 3.45/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_5916,c_7753]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_9352,plain,
% 3.45/1.01      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_7760,c_42]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_9355,plain,
% 3.45/1.01      ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top
% 3.45/1.01      | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.45/1.01      | v2_struct_0(sK3) = iProver_top
% 3.45/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.45/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_9352,c_5894]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6204,plain,
% 3.45/1.01      ( r2_hidden(sK0(sK4),sK4) | v1_xboole_0(sK4) ),
% 3.45/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6205,plain,
% 3.45/1.01      ( r2_hidden(sK0(sK4),sK4) = iProver_top
% 3.45/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_6204]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6374,plain,
% 3.45/1.01      ( ~ r1_tarski(sK4,X0)
% 3.45/1.01      | r2_hidden(sK0(sK4),X0)
% 3.45/1.01      | ~ r2_hidden(sK0(sK4),sK4) ),
% 3.45/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6931,plain,
% 3.45/1.01      ( ~ r1_tarski(sK4,u1_struct_0(X0))
% 3.45/1.01      | r2_hidden(sK0(sK4),u1_struct_0(X0))
% 3.45/1.01      | ~ r2_hidden(sK0(sK4),sK4) ),
% 3.45/1.01      inference(instantiation,[status(thm)],[c_6374]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6933,plain,
% 3.45/1.01      ( r1_tarski(sK4,u1_struct_0(X0)) != iProver_top
% 3.45/1.01      | r2_hidden(sK0(sK4),u1_struct_0(X0)) = iProver_top
% 3.45/1.01      | r2_hidden(sK0(sK4),sK4) != iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_6931]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6935,plain,
% 3.45/1.01      ( r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
% 3.45/1.01      | r2_hidden(sK0(sK4),u1_struct_0(sK3)) = iProver_top
% 3.45/1.01      | r2_hidden(sK0(sK4),sK4) != iProver_top ),
% 3.45/1.01      inference(instantiation,[status(thm)],[c_6933]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6274,plain,
% 3.45/1.01      ( m1_subset_1(X0,u1_struct_0(X1))
% 3.45/1.01      | ~ r2_hidden(X0,u1_struct_0(X1)) ),
% 3.45/1.01      inference(instantiation,[status(thm)],[c_229]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6932,plain,
% 3.45/1.01      ( m1_subset_1(sK0(sK4),u1_struct_0(X0))
% 3.45/1.01      | ~ r2_hidden(sK0(sK4),u1_struct_0(X0)) ),
% 3.45/1.01      inference(instantiation,[status(thm)],[c_6274]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6937,plain,
% 3.45/1.01      ( m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
% 3.45/1.01      | r2_hidden(sK0(sK4),u1_struct_0(X0)) != iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_6932]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6939,plain,
% 3.45/1.01      ( m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
% 3.45/1.01      | r2_hidden(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.45/1.01      inference(instantiation,[status(thm)],[c_6937]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_9963,plain,
% 3.45/1.01      ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_9355,c_38,c_39,c_41,c_42,c_6205,c_6579,c_6935,c_6939]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_13655,plain,
% 3.45/1.01      ( v2_tex_2(sK4,sK3) = iProver_top ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_13650,c_9963]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_14720,plain,
% 3.45/1.01      ( u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_13655,c_8324]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_14770,plain,
% 3.45/1.01      ( v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 3.45/1.01      | v2_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 3.45/1.01      | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 3.45/1.01      | v1_zfmisc_1(sK4) = iProver_top
% 3.45/1.01      | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_14720,c_5884]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_5895,plain,
% 3.45/1.01      ( v2_tex_2(X0,X1) != iProver_top
% 3.45/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.45/1.01      | v2_struct_0(X1) = iProver_top
% 3.45/1.01      | v2_struct_0(sK2(X1,X0)) != iProver_top
% 3.45/1.01      | v2_pre_topc(X1) != iProver_top
% 3.45/1.01      | l1_pre_topc(X1) != iProver_top
% 3.45/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7844,plain,
% 3.45/1.01      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.45/1.01      | v2_struct_0(sK2(sK3,sK4)) != iProver_top
% 3.45/1.01      | v2_struct_0(sK3) = iProver_top
% 3.45/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.45/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.45/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_5891,c_5895]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_8448,plain,
% 3.45/1.01      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.45/1.01      | v2_struct_0(sK2(sK3,sK4)) != iProver_top ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_7844,c_38,c_39,c_41,c_42]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_5896,plain,
% 3.45/1.01      ( v2_tex_2(X0,X1) != iProver_top
% 3.45/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.45/1.01      | v2_struct_0(X1) = iProver_top
% 3.45/1.01      | v1_tdlat_3(sK2(X1,X0)) = iProver_top
% 3.45/1.01      | v2_pre_topc(X1) != iProver_top
% 3.45/1.01      | l1_pre_topc(X1) != iProver_top
% 3.45/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7999,plain,
% 3.45/1.01      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.45/1.01      | v2_struct_0(sK3) = iProver_top
% 3.45/1.01      | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
% 3.45/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.45/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.45/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_5891,c_5896]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_8214,plain,
% 3.45/1.01      ( v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
% 3.45/1.01      | v2_tex_2(sK4,sK3) != iProver_top ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_7999,c_38,c_39,c_41,c_42]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_8215,plain,
% 3.45/1.01      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.45/1.01      | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top ),
% 3.45/1.01      inference(renaming,[status(thm)],[c_8214]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_30,negated_conjecture,
% 3.45/1.01      ( ~ v2_tex_2(sK4,sK3) | ~ v1_zfmisc_1(sK4) ),
% 3.45/1.01      inference(cnf_transformation,[],[f100]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_45,plain,
% 3.45/1.01      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.45/1.01      | v1_zfmisc_1(sK4) != iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(contradiction,plain,
% 3.45/1.01      ( $false ),
% 3.45/1.01      inference(minisat,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_14770,c_13655,c_8867,c_8461,c_8448,c_8215,c_45,c_41]) ).
% 3.45/1.01  
% 3.45/1.01  
% 3.45/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.45/1.01  
% 3.45/1.01  ------                               Statistics
% 3.45/1.01  
% 3.45/1.01  ------ General
% 3.45/1.01  
% 3.45/1.01  abstr_ref_over_cycles:                  0
% 3.45/1.01  abstr_ref_under_cycles:                 0
% 3.45/1.01  gc_basic_clause_elim:                   0
% 3.45/1.01  forced_gc_time:                         0
% 3.45/1.01  parsing_time:                           0.01
% 3.45/1.01  unif_index_cands_time:                  0.
% 3.45/1.01  unif_index_add_time:                    0.
% 3.45/1.01  orderings_time:                         0.
% 3.45/1.01  out_proof_time:                         0.011
% 3.45/1.01  total_time:                             0.384
% 3.45/1.01  num_of_symbols:                         54
% 3.45/1.01  num_of_terms:                           7483
% 3.45/1.01  
% 3.45/1.01  ------ Preprocessing
% 3.45/1.01  
% 3.45/1.01  num_of_splits:                          0
% 3.45/1.01  num_of_split_atoms:                     0
% 3.45/1.01  num_of_reused_defs:                     0
% 3.45/1.01  num_eq_ax_congr_red:                    32
% 3.45/1.01  num_of_sem_filtered_clauses:            1
% 3.45/1.01  num_of_subtypes:                        0
% 3.45/1.01  monotx_restored_types:                  0
% 3.45/1.01  sat_num_of_epr_types:                   0
% 3.45/1.01  sat_num_of_non_cyclic_types:            0
% 3.45/1.01  sat_guarded_non_collapsed_types:        0
% 3.45/1.01  num_pure_diseq_elim:                    0
% 3.45/1.01  simp_replaced_by:                       0
% 3.45/1.01  res_preprocessed:                       173
% 3.45/1.01  prep_upred:                             0
% 3.45/1.01  prep_unflattend:                        214
% 3.45/1.01  smt_new_axioms:                         0
% 3.45/1.01  pred_elim_cands:                        12
% 3.45/1.01  pred_elim:                              2
% 3.45/1.01  pred_elim_cl:                           2
% 3.45/1.01  pred_elim_cycles:                       18
% 3.45/1.01  merged_defs:                            24
% 3.45/1.01  merged_defs_ncl:                        0
% 3.45/1.01  bin_hyper_res:                          24
% 3.45/1.01  prep_cycles:                            4
% 3.45/1.01  pred_elim_time:                         0.076
% 3.45/1.01  splitting_time:                         0.
% 3.45/1.01  sem_filter_time:                        0.
% 3.45/1.01  monotx_time:                            0.
% 3.45/1.01  subtype_inf_time:                       0.
% 3.45/1.01  
% 3.45/1.01  ------ Problem properties
% 3.45/1.01  
% 3.45/1.01  clauses:                                34
% 3.45/1.01  conjectures:                            8
% 3.45/1.01  epr:                                    18
% 3.45/1.01  horn:                                   21
% 3.45/1.01  ground:                                 8
% 3.45/1.01  unary:                                  7
% 3.45/1.01  binary:                                 11
% 3.45/1.01  lits:                                   101
% 3.45/1.01  lits_eq:                                3
% 3.45/1.01  fd_pure:                                0
% 3.45/1.01  fd_pseudo:                              0
% 3.45/1.01  fd_cond:                                0
% 3.45/1.01  fd_pseudo_cond:                         1
% 3.45/1.01  ac_symbols:                             0
% 3.45/1.01  
% 3.45/1.01  ------ Propositional Solver
% 3.45/1.01  
% 3.45/1.01  prop_solver_calls:                      29
% 3.45/1.01  prop_fast_solver_calls:                 2558
% 3.45/1.01  smt_solver_calls:                       0
% 3.45/1.01  smt_fast_solver_calls:                  0
% 3.45/1.01  prop_num_of_clauses:                    3974
% 3.45/1.01  prop_preprocess_simplified:             10469
% 3.45/1.01  prop_fo_subsumed:                       185
% 3.45/1.01  prop_solver_time:                       0.
% 3.45/1.01  smt_solver_time:                        0.
% 3.45/1.01  smt_fast_solver_time:                   0.
% 3.45/1.01  prop_fast_solver_time:                  0.
% 3.45/1.01  prop_unsat_core_time:                   0.
% 3.45/1.01  
% 3.45/1.01  ------ QBF
% 3.45/1.01  
% 3.45/1.01  qbf_q_res:                              0
% 3.45/1.01  qbf_num_tautologies:                    0
% 3.45/1.01  qbf_prep_cycles:                        0
% 3.45/1.01  
% 3.45/1.01  ------ BMC1
% 3.45/1.01  
% 3.45/1.01  bmc1_current_bound:                     -1
% 3.45/1.01  bmc1_last_solved_bound:                 -1
% 3.45/1.01  bmc1_unsat_core_size:                   -1
% 3.45/1.01  bmc1_unsat_core_parents_size:           -1
% 3.45/1.01  bmc1_merge_next_fun:                    0
% 3.45/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.45/1.01  
% 3.45/1.01  ------ Instantiation
% 3.45/1.01  
% 3.45/1.01  inst_num_of_clauses:                    897
% 3.45/1.01  inst_num_in_passive:                    448
% 3.45/1.01  inst_num_in_active:                     448
% 3.45/1.01  inst_num_in_unprocessed:                1
% 3.45/1.01  inst_num_of_loops:                      610
% 3.45/1.01  inst_num_of_learning_restarts:          0
% 3.45/1.01  inst_num_moves_active_passive:          158
% 3.45/1.01  inst_lit_activity:                      0
% 3.45/1.01  inst_lit_activity_moves:                0
% 3.45/1.01  inst_num_tautologies:                   0
% 3.45/1.01  inst_num_prop_implied:                  0
% 3.45/1.01  inst_num_existing_simplified:           0
% 3.45/1.01  inst_num_eq_res_simplified:             0
% 3.45/1.01  inst_num_child_elim:                    0
% 3.45/1.01  inst_num_of_dismatching_blockings:      585
% 3.45/1.01  inst_num_of_non_proper_insts:           1046
% 3.45/1.01  inst_num_of_duplicates:                 0
% 3.45/1.01  inst_inst_num_from_inst_to_res:         0
% 3.45/1.01  inst_dismatching_checking_time:         0.
% 3.45/1.01  
% 3.45/1.01  ------ Resolution
% 3.45/1.01  
% 3.45/1.01  res_num_of_clauses:                     0
% 3.45/1.01  res_num_in_passive:                     0
% 3.45/1.01  res_num_in_active:                      0
% 3.45/1.01  res_num_of_loops:                       177
% 3.45/1.01  res_forward_subset_subsumed:            170
% 3.45/1.01  res_backward_subset_subsumed:           0
% 3.45/1.01  res_forward_subsumed:                   1
% 3.45/1.01  res_backward_subsumed:                  1
% 3.45/1.01  res_forward_subsumption_resolution:     2
% 3.45/1.01  res_backward_subsumption_resolution:    2
% 3.45/1.01  res_clause_to_clause_subsumption:       694
% 3.45/1.01  res_orphan_elimination:                 0
% 3.45/1.01  res_tautology_del:                      151
% 3.45/1.01  res_num_eq_res_simplified:              0
% 3.45/1.01  res_num_sel_changes:                    0
% 3.45/1.01  res_moves_from_active_to_pass:          0
% 3.45/1.01  
% 3.45/1.01  ------ Superposition
% 3.45/1.01  
% 3.45/1.01  sup_time_total:                         0.
% 3.45/1.01  sup_time_generating:                    0.
% 3.45/1.01  sup_time_sim_full:                      0.
% 3.45/1.01  sup_time_sim_immed:                     0.
% 3.45/1.01  
% 3.45/1.01  sup_num_of_clauses:                     221
% 3.45/1.01  sup_num_in_active:                      109
% 3.45/1.01  sup_num_in_passive:                     112
% 3.45/1.01  sup_num_of_loops:                       121
% 3.45/1.01  sup_fw_superposition:                   142
% 3.45/1.01  sup_bw_superposition:                   154
% 3.45/1.01  sup_immediate_simplified:               42
% 3.45/1.01  sup_given_eliminated:                   0
% 3.45/1.01  comparisons_done:                       0
% 3.45/1.01  comparisons_avoided:                    11
% 3.45/1.01  
% 3.45/1.01  ------ Simplifications
% 3.45/1.01  
% 3.45/1.01  
% 3.45/1.01  sim_fw_subset_subsumed:                 17
% 3.45/1.01  sim_bw_subset_subsumed:                 16
% 3.45/1.01  sim_fw_subsumed:                        13
% 3.45/1.01  sim_bw_subsumed:                        4
% 3.45/1.01  sim_fw_subsumption_res:                 1
% 3.45/1.01  sim_bw_subsumption_res:                 0
% 3.45/1.01  sim_tautology_del:                      19
% 3.45/1.01  sim_eq_tautology_del:                   4
% 3.45/1.01  sim_eq_res_simp:                        0
% 3.45/1.01  sim_fw_demodulated:                     1
% 3.45/1.01  sim_bw_demodulated:                     5
% 3.45/1.01  sim_light_normalised:                   10
% 3.45/1.01  sim_joinable_taut:                      0
% 3.45/1.01  sim_joinable_simp:                      0
% 3.45/1.01  sim_ac_normalised:                      0
% 3.45/1.01  sim_smt_subsumption:                    0
% 3.45/1.01  
%------------------------------------------------------------------------------
