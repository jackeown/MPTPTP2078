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
% DateTime   : Thu Dec  3 12:26:41 EST 2020

% Result     : Theorem 7.53s
% Output     : CNFRefutation 7.53s
% Verified   : 
% Statistics : Number of formulae       :  169 (1056 expanded)
%              Number of clauses        :   82 ( 299 expanded)
%              Number of leaves         :   22 ( 254 expanded)
%              Depth                    :   19
%              Number of atoms          :  664 (4930 expanded)
%              Number of equality atoms :  176 ( 499 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v1_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ~ v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v1_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f48,f66,f65])).

fof(f103,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f67])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f61])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f62,f63])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f99,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f100,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f102,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f104,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f54,f55])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f75,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f101,plain,(
    v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f91,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v1_tdlat_3(X1) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f87,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f84,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f86,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f85,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3136,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3140,plain,
    ( v2_tex_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(sK2(X1,X0),X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4945,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | r1_tarski(sK2(sK3,sK4),sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3136,c_3140])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_37,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_38,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_40,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1514,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_31])).

cnf(c_1515,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK2(sK3,sK4),sK4)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1514])).

cnf(c_1516,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK2(sK3,sK4),sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1515])).

cnf(c_5609,plain,
    ( r1_tarski(sK2(sK3,sK4),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4945,c_37,c_38,c_40,c_41,c_1516])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3155,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3157,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3609,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_3157])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3153,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4349,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3609,c_3153])).

cnf(c_5615,plain,
    ( sK2(sK3,sK4) = sK4
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5609,c_4349])).

cnf(c_34,negated_conjecture,
    ( v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_39,plain,
    ( v1_tdlat_3(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_42,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_15,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3470,plain,
    ( m1_pre_topc(k1_pre_topc(sK3,sK4),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3471,plain,
    ( m1_pre_topc(k1_pre_topc(sK3,sK4),sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3470])).

cnf(c_23,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_704,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X2)
    | ~ v1_tdlat_3(X1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_24])).

cnf(c_705,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_704])).

cnf(c_3647,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK3,sK4),X0)
    | ~ v1_tdlat_3(X0)
    | v1_tdlat_3(k1_pre_topc(sK3,sK4))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_3648,plain,
    ( m1_pre_topc(k1_pre_topc(sK3,sK4),X0) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v1_tdlat_3(k1_pre_topc(sK3,sK4)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3647])).

cnf(c_3650,plain,
    ( m1_pre_topc(k1_pre_topc(sK3,sK4),sK3) != iProver_top
    | v1_tdlat_3(k1_pre_topc(sK3,sK4)) = iProver_top
    | v1_tdlat_3(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3648])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3144,plain,
    ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4757,plain,
    ( u1_struct_0(k1_pre_topc(sK3,sK4)) = sK4
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3136,c_3144])).

cnf(c_3475,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(k1_pre_topc(sK3,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_5350,plain,
    ( u1_struct_0(k1_pre_topc(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4757,c_33,c_32,c_3475])).

cnf(c_25,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_206,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_tex_2(u1_struct_0(X0),X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_22])).

cnf(c_207,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_206])).

cnf(c_3130,plain,
    ( v2_tex_2(u1_struct_0(X0),X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_207])).

cnf(c_5355,plain,
    ( v2_tex_2(sK4,X0) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK3,sK4),X0) != iProver_top
    | v1_tdlat_3(k1_pre_topc(sK3,sK4)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k1_pre_topc(sK3,sK4)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5350,c_3130])).

cnf(c_5457,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK3,sK4),sK3) != iProver_top
    | v1_tdlat_3(k1_pre_topc(sK3,sK4)) != iProver_top
    | v2_struct_0(k1_pre_topc(sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5355])).

cnf(c_16,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_18,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_411,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_16,c_18])).

cnf(c_3128,plain,
    ( v2_struct_0(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_5359,plain,
    ( v2_struct_0(k1_pre_topc(sK3,sK4)) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK3,sK4)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5350,c_3128])).

cnf(c_3146,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4917,plain,
    ( m1_pre_topc(k1_pre_topc(sK3,sK4),sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3136,c_3146])).

cnf(c_5480,plain,
    ( m1_pre_topc(k1_pre_topc(sK3,sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4917,c_40,c_41,c_3471])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3145,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5486,plain,
    ( l1_pre_topc(k1_pre_topc(sK3,sK4)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5480,c_3145])).

cnf(c_5635,plain,
    ( sK2(sK3,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5615,c_37,c_39,c_40,c_41,c_42,c_3471,c_3650,c_5457,c_5359,c_5486])).

cnf(c_27,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,sK2(X1,X0))) != sK2(X1,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3141,plain,
    ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
    | v2_tex_2(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5640,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK4)) != sK2(sK3,sK4)
    | v2_tex_2(sK4,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5635,c_3141])).

cnf(c_5647,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK4)) != sK4
    | v2_tex_2(sK4,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5640,c_5635])).

cnf(c_18882,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK4)) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5647,c_37,c_38,c_40,c_41,c_42])).

cnf(c_6143,plain,
    ( v1_xboole_0(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5359,c_37,c_39,c_40,c_41,c_42,c_3471,c_3650,c_5457,c_5486])).

cnf(c_14,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_21,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(resolution,[status(thm)],[c_14,c_21])).

cnf(c_3127,plain,
    ( k2_pre_topc(X0,X1) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_4154,plain,
    ( k2_pre_topc(sK3,sK4) = sK4
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3136,c_3127])).

cnf(c_4359,plain,
    ( k2_pre_topc(sK3,sK4) = sK4
    | v1_xboole_0(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4154,c_38,c_40])).

cnf(c_6149,plain,
    ( k2_pre_topc(sK3,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_6143,c_4359])).

cnf(c_18884,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK4) != sK4 ),
    inference(light_normalisation,[status(thm)],[c_18882,c_6149])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3147,plain,
    ( k9_subset_1(X0,X1,X1) = X1
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3716,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_3136,c_3147])).

cnf(c_18885,plain,
    ( sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_18884,c_3716])).

cnf(c_18886,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_18885])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.53/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.53/1.51  
% 7.53/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.53/1.51  
% 7.53/1.51  ------  iProver source info
% 7.53/1.51  
% 7.53/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.53/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.53/1.51  git: non_committed_changes: false
% 7.53/1.51  git: last_make_outside_of_git: false
% 7.53/1.51  
% 7.53/1.51  ------ 
% 7.53/1.51  
% 7.53/1.51  ------ Input Options
% 7.53/1.51  
% 7.53/1.51  --out_options                           all
% 7.53/1.51  --tptp_safe_out                         true
% 7.53/1.51  --problem_path                          ""
% 7.53/1.51  --include_path                          ""
% 7.53/1.51  --clausifier                            res/vclausify_rel
% 7.53/1.51  --clausifier_options                    --mode clausify
% 7.53/1.51  --stdin                                 false
% 7.53/1.51  --stats_out                             all
% 7.53/1.51  
% 7.53/1.51  ------ General Options
% 7.53/1.51  
% 7.53/1.51  --fof                                   false
% 7.53/1.51  --time_out_real                         305.
% 7.53/1.51  --time_out_virtual                      -1.
% 7.53/1.51  --symbol_type_check                     false
% 7.53/1.51  --clausify_out                          false
% 7.53/1.51  --sig_cnt_out                           false
% 7.53/1.51  --trig_cnt_out                          false
% 7.53/1.51  --trig_cnt_out_tolerance                1.
% 7.53/1.51  --trig_cnt_out_sk_spl                   false
% 7.53/1.51  --abstr_cl_out                          false
% 7.53/1.51  
% 7.53/1.51  ------ Global Options
% 7.53/1.51  
% 7.53/1.51  --schedule                              default
% 7.53/1.51  --add_important_lit                     false
% 7.53/1.51  --prop_solver_per_cl                    1000
% 7.53/1.51  --min_unsat_core                        false
% 7.53/1.51  --soft_assumptions                      false
% 7.53/1.51  --soft_lemma_size                       3
% 7.53/1.51  --prop_impl_unit_size                   0
% 7.53/1.51  --prop_impl_unit                        []
% 7.53/1.51  --share_sel_clauses                     true
% 7.53/1.51  --reset_solvers                         false
% 7.53/1.51  --bc_imp_inh                            [conj_cone]
% 7.53/1.51  --conj_cone_tolerance                   3.
% 7.53/1.51  --extra_neg_conj                        none
% 7.53/1.51  --large_theory_mode                     true
% 7.53/1.51  --prolific_symb_bound                   200
% 7.53/1.51  --lt_threshold                          2000
% 7.53/1.51  --clause_weak_htbl                      true
% 7.53/1.51  --gc_record_bc_elim                     false
% 7.53/1.51  
% 7.53/1.51  ------ Preprocessing Options
% 7.53/1.51  
% 7.53/1.51  --preprocessing_flag                    true
% 7.53/1.51  --time_out_prep_mult                    0.1
% 7.53/1.51  --splitting_mode                        input
% 7.53/1.51  --splitting_grd                         true
% 7.53/1.51  --splitting_cvd                         false
% 7.53/1.51  --splitting_cvd_svl                     false
% 7.53/1.51  --splitting_nvd                         32
% 7.53/1.51  --sub_typing                            true
% 7.53/1.51  --prep_gs_sim                           true
% 7.53/1.51  --prep_unflatten                        true
% 7.53/1.51  --prep_res_sim                          true
% 7.53/1.51  --prep_upred                            true
% 7.53/1.51  --prep_sem_filter                       exhaustive
% 7.53/1.51  --prep_sem_filter_out                   false
% 7.53/1.51  --pred_elim                             true
% 7.53/1.51  --res_sim_input                         true
% 7.53/1.51  --eq_ax_congr_red                       true
% 7.53/1.51  --pure_diseq_elim                       true
% 7.53/1.51  --brand_transform                       false
% 7.53/1.51  --non_eq_to_eq                          false
% 7.53/1.51  --prep_def_merge                        true
% 7.53/1.51  --prep_def_merge_prop_impl              false
% 7.53/1.51  --prep_def_merge_mbd                    true
% 7.53/1.51  --prep_def_merge_tr_red                 false
% 7.53/1.51  --prep_def_merge_tr_cl                  false
% 7.53/1.51  --smt_preprocessing                     true
% 7.53/1.51  --smt_ac_axioms                         fast
% 7.53/1.51  --preprocessed_out                      false
% 7.53/1.51  --preprocessed_stats                    false
% 7.53/1.51  
% 7.53/1.51  ------ Abstraction refinement Options
% 7.53/1.51  
% 7.53/1.51  --abstr_ref                             []
% 7.53/1.51  --abstr_ref_prep                        false
% 7.53/1.51  --abstr_ref_until_sat                   false
% 7.53/1.51  --abstr_ref_sig_restrict                funpre
% 7.53/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.53/1.51  --abstr_ref_under                       []
% 7.53/1.51  
% 7.53/1.51  ------ SAT Options
% 7.53/1.51  
% 7.53/1.51  --sat_mode                              false
% 7.53/1.51  --sat_fm_restart_options                ""
% 7.53/1.51  --sat_gr_def                            false
% 7.53/1.51  --sat_epr_types                         true
% 7.53/1.51  --sat_non_cyclic_types                  false
% 7.53/1.51  --sat_finite_models                     false
% 7.53/1.51  --sat_fm_lemmas                         false
% 7.53/1.51  --sat_fm_prep                           false
% 7.53/1.51  --sat_fm_uc_incr                        true
% 7.53/1.51  --sat_out_model                         small
% 7.53/1.51  --sat_out_clauses                       false
% 7.53/1.51  
% 7.53/1.51  ------ QBF Options
% 7.53/1.51  
% 7.53/1.51  --qbf_mode                              false
% 7.53/1.51  --qbf_elim_univ                         false
% 7.53/1.51  --qbf_dom_inst                          none
% 7.53/1.51  --qbf_dom_pre_inst                      false
% 7.53/1.51  --qbf_sk_in                             false
% 7.53/1.51  --qbf_pred_elim                         true
% 7.53/1.51  --qbf_split                             512
% 7.53/1.51  
% 7.53/1.51  ------ BMC1 Options
% 7.53/1.51  
% 7.53/1.51  --bmc1_incremental                      false
% 7.53/1.51  --bmc1_axioms                           reachable_all
% 7.53/1.51  --bmc1_min_bound                        0
% 7.53/1.51  --bmc1_max_bound                        -1
% 7.53/1.51  --bmc1_max_bound_default                -1
% 7.53/1.51  --bmc1_symbol_reachability              true
% 7.53/1.51  --bmc1_property_lemmas                  false
% 7.53/1.51  --bmc1_k_induction                      false
% 7.53/1.51  --bmc1_non_equiv_states                 false
% 7.53/1.51  --bmc1_deadlock                         false
% 7.53/1.51  --bmc1_ucm                              false
% 7.53/1.51  --bmc1_add_unsat_core                   none
% 7.53/1.51  --bmc1_unsat_core_children              false
% 7.53/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.53/1.51  --bmc1_out_stat                         full
% 7.53/1.51  --bmc1_ground_init                      false
% 7.53/1.51  --bmc1_pre_inst_next_state              false
% 7.53/1.51  --bmc1_pre_inst_state                   false
% 7.53/1.51  --bmc1_pre_inst_reach_state             false
% 7.53/1.51  --bmc1_out_unsat_core                   false
% 7.53/1.51  --bmc1_aig_witness_out                  false
% 7.53/1.51  --bmc1_verbose                          false
% 7.53/1.51  --bmc1_dump_clauses_tptp                false
% 7.53/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.53/1.51  --bmc1_dump_file                        -
% 7.53/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.53/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.53/1.51  --bmc1_ucm_extend_mode                  1
% 7.53/1.51  --bmc1_ucm_init_mode                    2
% 7.53/1.51  --bmc1_ucm_cone_mode                    none
% 7.53/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.53/1.51  --bmc1_ucm_relax_model                  4
% 7.53/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.53/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.53/1.51  --bmc1_ucm_layered_model                none
% 7.53/1.51  --bmc1_ucm_max_lemma_size               10
% 7.53/1.51  
% 7.53/1.51  ------ AIG Options
% 7.53/1.51  
% 7.53/1.51  --aig_mode                              false
% 7.53/1.51  
% 7.53/1.51  ------ Instantiation Options
% 7.53/1.51  
% 7.53/1.51  --instantiation_flag                    true
% 7.53/1.51  --inst_sos_flag                         false
% 7.53/1.51  --inst_sos_phase                        true
% 7.53/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.53/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.53/1.51  --inst_lit_sel_side                     num_symb
% 7.53/1.51  --inst_solver_per_active                1400
% 7.53/1.51  --inst_solver_calls_frac                1.
% 7.53/1.51  --inst_passive_queue_type               priority_queues
% 7.53/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.53/1.51  --inst_passive_queues_freq              [25;2]
% 7.53/1.51  --inst_dismatching                      true
% 7.53/1.51  --inst_eager_unprocessed_to_passive     true
% 7.53/1.51  --inst_prop_sim_given                   true
% 7.53/1.51  --inst_prop_sim_new                     false
% 7.53/1.51  --inst_subs_new                         false
% 7.53/1.51  --inst_eq_res_simp                      false
% 7.53/1.51  --inst_subs_given                       false
% 7.53/1.51  --inst_orphan_elimination               true
% 7.53/1.51  --inst_learning_loop_flag               true
% 7.53/1.51  --inst_learning_start                   3000
% 7.53/1.51  --inst_learning_factor                  2
% 7.53/1.51  --inst_start_prop_sim_after_learn       3
% 7.53/1.51  --inst_sel_renew                        solver
% 7.53/1.51  --inst_lit_activity_flag                true
% 7.53/1.51  --inst_restr_to_given                   false
% 7.53/1.51  --inst_activity_threshold               500
% 7.53/1.51  --inst_out_proof                        true
% 7.53/1.51  
% 7.53/1.51  ------ Resolution Options
% 7.53/1.51  
% 7.53/1.51  --resolution_flag                       true
% 7.53/1.51  --res_lit_sel                           adaptive
% 7.53/1.51  --res_lit_sel_side                      none
% 7.53/1.51  --res_ordering                          kbo
% 7.53/1.51  --res_to_prop_solver                    active
% 7.53/1.51  --res_prop_simpl_new                    false
% 7.53/1.51  --res_prop_simpl_given                  true
% 7.53/1.51  --res_passive_queue_type                priority_queues
% 7.53/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.53/1.51  --res_passive_queues_freq               [15;5]
% 7.53/1.51  --res_forward_subs                      full
% 7.53/1.51  --res_backward_subs                     full
% 7.53/1.51  --res_forward_subs_resolution           true
% 7.53/1.51  --res_backward_subs_resolution          true
% 7.53/1.51  --res_orphan_elimination                true
% 7.53/1.51  --res_time_limit                        2.
% 7.53/1.51  --res_out_proof                         true
% 7.53/1.51  
% 7.53/1.51  ------ Superposition Options
% 7.53/1.51  
% 7.53/1.51  --superposition_flag                    true
% 7.53/1.51  --sup_passive_queue_type                priority_queues
% 7.53/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.53/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.53/1.51  --demod_completeness_check              fast
% 7.53/1.51  --demod_use_ground                      true
% 7.53/1.51  --sup_to_prop_solver                    passive
% 7.53/1.51  --sup_prop_simpl_new                    true
% 7.53/1.51  --sup_prop_simpl_given                  true
% 7.53/1.51  --sup_fun_splitting                     false
% 7.53/1.51  --sup_smt_interval                      50000
% 7.53/1.51  
% 7.53/1.51  ------ Superposition Simplification Setup
% 7.53/1.51  
% 7.53/1.51  --sup_indices_passive                   []
% 7.53/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.53/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.53/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.53/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.53/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.53/1.51  --sup_full_bw                           [BwDemod]
% 7.53/1.51  --sup_immed_triv                        [TrivRules]
% 7.53/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.53/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.53/1.51  --sup_immed_bw_main                     []
% 7.53/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.53/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.53/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.53/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.53/1.51  
% 7.53/1.51  ------ Combination Options
% 7.53/1.51  
% 7.53/1.51  --comb_res_mult                         3
% 7.53/1.51  --comb_sup_mult                         2
% 7.53/1.51  --comb_inst_mult                        10
% 7.53/1.51  
% 7.53/1.51  ------ Debug Options
% 7.53/1.51  
% 7.53/1.51  --dbg_backtrace                         false
% 7.53/1.51  --dbg_dump_prop_clauses                 false
% 7.53/1.51  --dbg_dump_prop_clauses_file            -
% 7.53/1.51  --dbg_out_stat                          false
% 7.53/1.51  ------ Parsing...
% 7.53/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.53/1.51  
% 7.53/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.53/1.51  
% 7.53/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.53/1.51  
% 7.53/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.53/1.51  ------ Proving...
% 7.53/1.51  ------ Problem Properties 
% 7.53/1.51  
% 7.53/1.51  
% 7.53/1.51  clauses                                 33
% 7.53/1.51  conjectures                             6
% 7.53/1.51  EPR                                     16
% 7.53/1.51  Horn                                    23
% 7.53/1.51  unary                                   8
% 7.53/1.51  binary                                  6
% 7.53/1.51  lits                                    101
% 7.53/1.51  lits eq                                 6
% 7.53/1.51  fd_pure                                 0
% 7.53/1.51  fd_pseudo                               0
% 7.53/1.51  fd_cond                                 0
% 7.53/1.51  fd_pseudo_cond                          1
% 7.53/1.51  AC symbols                              0
% 7.53/1.51  
% 7.53/1.51  ------ Schedule dynamic 5 is on 
% 7.53/1.51  
% 7.53/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.53/1.51  
% 7.53/1.51  
% 7.53/1.51  ------ 
% 7.53/1.51  Current options:
% 7.53/1.51  ------ 
% 7.53/1.51  
% 7.53/1.51  ------ Input Options
% 7.53/1.51  
% 7.53/1.51  --out_options                           all
% 7.53/1.51  --tptp_safe_out                         true
% 7.53/1.51  --problem_path                          ""
% 7.53/1.51  --include_path                          ""
% 7.53/1.51  --clausifier                            res/vclausify_rel
% 7.53/1.51  --clausifier_options                    --mode clausify
% 7.53/1.51  --stdin                                 false
% 7.53/1.51  --stats_out                             all
% 7.53/1.51  
% 7.53/1.51  ------ General Options
% 7.53/1.51  
% 7.53/1.51  --fof                                   false
% 7.53/1.51  --time_out_real                         305.
% 7.53/1.51  --time_out_virtual                      -1.
% 7.53/1.51  --symbol_type_check                     false
% 7.53/1.51  --clausify_out                          false
% 7.53/1.51  --sig_cnt_out                           false
% 7.53/1.51  --trig_cnt_out                          false
% 7.53/1.51  --trig_cnt_out_tolerance                1.
% 7.53/1.51  --trig_cnt_out_sk_spl                   false
% 7.53/1.51  --abstr_cl_out                          false
% 7.53/1.51  
% 7.53/1.51  ------ Global Options
% 7.53/1.51  
% 7.53/1.51  --schedule                              default
% 7.53/1.51  --add_important_lit                     false
% 7.53/1.51  --prop_solver_per_cl                    1000
% 7.53/1.51  --min_unsat_core                        false
% 7.53/1.51  --soft_assumptions                      false
% 7.53/1.51  --soft_lemma_size                       3
% 7.53/1.51  --prop_impl_unit_size                   0
% 7.53/1.51  --prop_impl_unit                        []
% 7.53/1.51  --share_sel_clauses                     true
% 7.53/1.51  --reset_solvers                         false
% 7.53/1.51  --bc_imp_inh                            [conj_cone]
% 7.53/1.51  --conj_cone_tolerance                   3.
% 7.53/1.51  --extra_neg_conj                        none
% 7.53/1.51  --large_theory_mode                     true
% 7.53/1.51  --prolific_symb_bound                   200
% 7.53/1.51  --lt_threshold                          2000
% 7.53/1.51  --clause_weak_htbl                      true
% 7.53/1.51  --gc_record_bc_elim                     false
% 7.53/1.51  
% 7.53/1.51  ------ Preprocessing Options
% 7.53/1.51  
% 7.53/1.51  --preprocessing_flag                    true
% 7.53/1.51  --time_out_prep_mult                    0.1
% 7.53/1.51  --splitting_mode                        input
% 7.53/1.51  --splitting_grd                         true
% 7.53/1.51  --splitting_cvd                         false
% 7.53/1.51  --splitting_cvd_svl                     false
% 7.53/1.51  --splitting_nvd                         32
% 7.53/1.51  --sub_typing                            true
% 7.53/1.51  --prep_gs_sim                           true
% 7.53/1.51  --prep_unflatten                        true
% 7.53/1.51  --prep_res_sim                          true
% 7.53/1.51  --prep_upred                            true
% 7.53/1.51  --prep_sem_filter                       exhaustive
% 7.53/1.51  --prep_sem_filter_out                   false
% 7.53/1.51  --pred_elim                             true
% 7.53/1.51  --res_sim_input                         true
% 7.53/1.51  --eq_ax_congr_red                       true
% 7.53/1.51  --pure_diseq_elim                       true
% 7.53/1.51  --brand_transform                       false
% 7.53/1.51  --non_eq_to_eq                          false
% 7.53/1.51  --prep_def_merge                        true
% 7.53/1.51  --prep_def_merge_prop_impl              false
% 7.53/1.51  --prep_def_merge_mbd                    true
% 7.53/1.51  --prep_def_merge_tr_red                 false
% 7.53/1.51  --prep_def_merge_tr_cl                  false
% 7.53/1.51  --smt_preprocessing                     true
% 7.53/1.51  --smt_ac_axioms                         fast
% 7.53/1.51  --preprocessed_out                      false
% 7.53/1.51  --preprocessed_stats                    false
% 7.53/1.51  
% 7.53/1.51  ------ Abstraction refinement Options
% 7.53/1.51  
% 7.53/1.51  --abstr_ref                             []
% 7.53/1.51  --abstr_ref_prep                        false
% 7.53/1.51  --abstr_ref_until_sat                   false
% 7.53/1.51  --abstr_ref_sig_restrict                funpre
% 7.53/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.53/1.51  --abstr_ref_under                       []
% 7.53/1.51  
% 7.53/1.51  ------ SAT Options
% 7.53/1.51  
% 7.53/1.51  --sat_mode                              false
% 7.53/1.51  --sat_fm_restart_options                ""
% 7.53/1.51  --sat_gr_def                            false
% 7.53/1.51  --sat_epr_types                         true
% 7.53/1.51  --sat_non_cyclic_types                  false
% 7.53/1.51  --sat_finite_models                     false
% 7.53/1.51  --sat_fm_lemmas                         false
% 7.53/1.51  --sat_fm_prep                           false
% 7.53/1.51  --sat_fm_uc_incr                        true
% 7.53/1.51  --sat_out_model                         small
% 7.53/1.51  --sat_out_clauses                       false
% 7.53/1.51  
% 7.53/1.51  ------ QBF Options
% 7.53/1.51  
% 7.53/1.51  --qbf_mode                              false
% 7.53/1.51  --qbf_elim_univ                         false
% 7.53/1.51  --qbf_dom_inst                          none
% 7.53/1.51  --qbf_dom_pre_inst                      false
% 7.53/1.51  --qbf_sk_in                             false
% 7.53/1.51  --qbf_pred_elim                         true
% 7.53/1.51  --qbf_split                             512
% 7.53/1.51  
% 7.53/1.51  ------ BMC1 Options
% 7.53/1.51  
% 7.53/1.51  --bmc1_incremental                      false
% 7.53/1.51  --bmc1_axioms                           reachable_all
% 7.53/1.51  --bmc1_min_bound                        0
% 7.53/1.51  --bmc1_max_bound                        -1
% 7.53/1.51  --bmc1_max_bound_default                -1
% 7.53/1.51  --bmc1_symbol_reachability              true
% 7.53/1.51  --bmc1_property_lemmas                  false
% 7.53/1.51  --bmc1_k_induction                      false
% 7.53/1.51  --bmc1_non_equiv_states                 false
% 7.53/1.51  --bmc1_deadlock                         false
% 7.53/1.51  --bmc1_ucm                              false
% 7.53/1.51  --bmc1_add_unsat_core                   none
% 7.53/1.51  --bmc1_unsat_core_children              false
% 7.53/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.53/1.51  --bmc1_out_stat                         full
% 7.53/1.51  --bmc1_ground_init                      false
% 7.53/1.51  --bmc1_pre_inst_next_state              false
% 7.53/1.51  --bmc1_pre_inst_state                   false
% 7.53/1.51  --bmc1_pre_inst_reach_state             false
% 7.53/1.51  --bmc1_out_unsat_core                   false
% 7.53/1.51  --bmc1_aig_witness_out                  false
% 7.53/1.51  --bmc1_verbose                          false
% 7.53/1.51  --bmc1_dump_clauses_tptp                false
% 7.53/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.53/1.51  --bmc1_dump_file                        -
% 7.53/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.53/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.53/1.51  --bmc1_ucm_extend_mode                  1
% 7.53/1.51  --bmc1_ucm_init_mode                    2
% 7.53/1.51  --bmc1_ucm_cone_mode                    none
% 7.53/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.53/1.51  --bmc1_ucm_relax_model                  4
% 7.53/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.53/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.53/1.51  --bmc1_ucm_layered_model                none
% 7.53/1.51  --bmc1_ucm_max_lemma_size               10
% 7.53/1.51  
% 7.53/1.51  ------ AIG Options
% 7.53/1.51  
% 7.53/1.51  --aig_mode                              false
% 7.53/1.51  
% 7.53/1.51  ------ Instantiation Options
% 7.53/1.51  
% 7.53/1.51  --instantiation_flag                    true
% 7.53/1.51  --inst_sos_flag                         false
% 7.53/1.51  --inst_sos_phase                        true
% 7.53/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.53/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.53/1.51  --inst_lit_sel_side                     none
% 7.53/1.51  --inst_solver_per_active                1400
% 7.53/1.51  --inst_solver_calls_frac                1.
% 7.53/1.51  --inst_passive_queue_type               priority_queues
% 7.53/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.53/1.51  --inst_passive_queues_freq              [25;2]
% 7.53/1.51  --inst_dismatching                      true
% 7.53/1.51  --inst_eager_unprocessed_to_passive     true
% 7.53/1.51  --inst_prop_sim_given                   true
% 7.53/1.51  --inst_prop_sim_new                     false
% 7.53/1.51  --inst_subs_new                         false
% 7.53/1.51  --inst_eq_res_simp                      false
% 7.53/1.51  --inst_subs_given                       false
% 7.53/1.51  --inst_orphan_elimination               true
% 7.53/1.51  --inst_learning_loop_flag               true
% 7.53/1.51  --inst_learning_start                   3000
% 7.53/1.51  --inst_learning_factor                  2
% 7.53/1.51  --inst_start_prop_sim_after_learn       3
% 7.53/1.51  --inst_sel_renew                        solver
% 7.53/1.51  --inst_lit_activity_flag                true
% 7.53/1.51  --inst_restr_to_given                   false
% 7.53/1.51  --inst_activity_threshold               500
% 7.53/1.51  --inst_out_proof                        true
% 7.53/1.51  
% 7.53/1.51  ------ Resolution Options
% 7.53/1.51  
% 7.53/1.51  --resolution_flag                       false
% 7.53/1.51  --res_lit_sel                           adaptive
% 7.53/1.51  --res_lit_sel_side                      none
% 7.53/1.51  --res_ordering                          kbo
% 7.53/1.51  --res_to_prop_solver                    active
% 7.53/1.51  --res_prop_simpl_new                    false
% 7.53/1.51  --res_prop_simpl_given                  true
% 7.53/1.51  --res_passive_queue_type                priority_queues
% 7.53/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.53/1.51  --res_passive_queues_freq               [15;5]
% 7.53/1.51  --res_forward_subs                      full
% 7.53/1.51  --res_backward_subs                     full
% 7.53/1.51  --res_forward_subs_resolution           true
% 7.53/1.51  --res_backward_subs_resolution          true
% 7.53/1.51  --res_orphan_elimination                true
% 7.53/1.51  --res_time_limit                        2.
% 7.53/1.51  --res_out_proof                         true
% 7.53/1.51  
% 7.53/1.51  ------ Superposition Options
% 7.53/1.51  
% 7.53/1.51  --superposition_flag                    true
% 7.53/1.51  --sup_passive_queue_type                priority_queues
% 7.53/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.53/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.53/1.51  --demod_completeness_check              fast
% 7.53/1.51  --demod_use_ground                      true
% 7.53/1.51  --sup_to_prop_solver                    passive
% 7.53/1.51  --sup_prop_simpl_new                    true
% 7.53/1.51  --sup_prop_simpl_given                  true
% 7.53/1.51  --sup_fun_splitting                     false
% 7.53/1.51  --sup_smt_interval                      50000
% 7.53/1.51  
% 7.53/1.51  ------ Superposition Simplification Setup
% 7.53/1.51  
% 7.53/1.51  --sup_indices_passive                   []
% 7.53/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.53/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.53/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.53/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.53/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.53/1.51  --sup_full_bw                           [BwDemod]
% 7.53/1.51  --sup_immed_triv                        [TrivRules]
% 7.53/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.53/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.53/1.51  --sup_immed_bw_main                     []
% 7.53/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.53/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.53/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.53/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.53/1.51  
% 7.53/1.51  ------ Combination Options
% 7.53/1.51  
% 7.53/1.51  --comb_res_mult                         3
% 7.53/1.51  --comb_sup_mult                         2
% 7.53/1.51  --comb_inst_mult                        10
% 7.53/1.51  
% 7.53/1.51  ------ Debug Options
% 7.53/1.51  
% 7.53/1.51  --dbg_backtrace                         false
% 7.53/1.51  --dbg_dump_prop_clauses                 false
% 7.53/1.51  --dbg_dump_prop_clauses_file            -
% 7.53/1.51  --dbg_out_stat                          false
% 7.53/1.51  
% 7.53/1.51  
% 7.53/1.51  
% 7.53/1.51  
% 7.53/1.51  ------ Proving...
% 7.53/1.51  
% 7.53/1.51  
% 7.53/1.51  % SZS status Theorem for theBenchmark.p
% 7.53/1.51  
% 7.53/1.51   Resolution empty clause
% 7.53/1.51  
% 7.53/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.53/1.51  
% 7.53/1.51  fof(f19,conjecture,(
% 7.53/1.51    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f20,negated_conjecture,(
% 7.53/1.51    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 7.53/1.51    inference(negated_conjecture,[],[f19])).
% 7.53/1.51  
% 7.53/1.51  fof(f47,plain,(
% 7.53/1.51    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.53/1.51    inference(ennf_transformation,[],[f20])).
% 7.53/1.51  
% 7.53/1.51  fof(f48,plain,(
% 7.53/1.51    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.53/1.51    inference(flattening,[],[f47])).
% 7.53/1.51  
% 7.53/1.51  fof(f66,plain,(
% 7.53/1.51    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.53/1.51    introduced(choice_axiom,[])).
% 7.53/1.51  
% 7.53/1.51  fof(f65,plain,(
% 7.53/1.51    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v1_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 7.53/1.51    introduced(choice_axiom,[])).
% 7.53/1.51  
% 7.53/1.51  fof(f67,plain,(
% 7.53/1.51    (~v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v1_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 7.53/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f48,f66,f65])).
% 7.53/1.51  
% 7.53/1.51  fof(f103,plain,(
% 7.53/1.51    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 7.53/1.51    inference(cnf_transformation,[],[f67])).
% 7.53/1.51  
% 7.53/1.51  fof(f18,axiom,(
% 7.53/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f45,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.53/1.51    inference(ennf_transformation,[],[f18])).
% 7.53/1.51  
% 7.53/1.51  fof(f46,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.53/1.51    inference(flattening,[],[f45])).
% 7.53/1.51  
% 7.53/1.51  fof(f61,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.53/1.51    inference(nnf_transformation,[],[f46])).
% 7.53/1.51  
% 7.53/1.51  fof(f62,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.53/1.51    inference(rectify,[],[f61])).
% 7.53/1.51  
% 7.53/1.51  fof(f63,plain,(
% 7.53/1.51    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.53/1.51    introduced(choice_axiom,[])).
% 7.53/1.51  
% 7.53/1.51  fof(f64,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.53/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f62,f63])).
% 7.53/1.51  
% 7.53/1.51  fof(f97,plain,(
% 7.53/1.51    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f64])).
% 7.53/1.51  
% 7.53/1.51  fof(f99,plain,(
% 7.53/1.51    ~v2_struct_0(sK3)),
% 7.53/1.51    inference(cnf_transformation,[],[f67])).
% 7.53/1.51  
% 7.53/1.51  fof(f100,plain,(
% 7.53/1.51    v2_pre_topc(sK3)),
% 7.53/1.51    inference(cnf_transformation,[],[f67])).
% 7.53/1.51  
% 7.53/1.51  fof(f102,plain,(
% 7.53/1.51    l1_pre_topc(sK3)),
% 7.53/1.51    inference(cnf_transformation,[],[f67])).
% 7.53/1.51  
% 7.53/1.51  fof(f104,plain,(
% 7.53/1.51    ~v2_tex_2(sK4,sK3)),
% 7.53/1.51    inference(cnf_transformation,[],[f67])).
% 7.53/1.51  
% 7.53/1.51  fof(f2,axiom,(
% 7.53/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f24,plain,(
% 7.53/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.53/1.51    inference(ennf_transformation,[],[f2])).
% 7.53/1.51  
% 7.53/1.51  fof(f53,plain,(
% 7.53/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.53/1.51    inference(nnf_transformation,[],[f24])).
% 7.53/1.51  
% 7.53/1.51  fof(f54,plain,(
% 7.53/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.53/1.51    inference(rectify,[],[f53])).
% 7.53/1.51  
% 7.53/1.51  fof(f55,plain,(
% 7.53/1.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.53/1.51    introduced(choice_axiom,[])).
% 7.53/1.51  
% 7.53/1.51  fof(f56,plain,(
% 7.53/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.53/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f54,f55])).
% 7.53/1.51  
% 7.53/1.51  fof(f71,plain,(
% 7.53/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f56])).
% 7.53/1.51  
% 7.53/1.51  fof(f1,axiom,(
% 7.53/1.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f49,plain,(
% 7.53/1.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.53/1.51    inference(nnf_transformation,[],[f1])).
% 7.53/1.51  
% 7.53/1.51  fof(f50,plain,(
% 7.53/1.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.53/1.51    inference(rectify,[],[f49])).
% 7.53/1.51  
% 7.53/1.51  fof(f51,plain,(
% 7.53/1.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.53/1.51    introduced(choice_axiom,[])).
% 7.53/1.51  
% 7.53/1.51  fof(f52,plain,(
% 7.53/1.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.53/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).
% 7.53/1.51  
% 7.53/1.51  fof(f68,plain,(
% 7.53/1.51    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f52])).
% 7.53/1.51  
% 7.53/1.51  fof(f3,axiom,(
% 7.53/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f57,plain,(
% 7.53/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.53/1.51    inference(nnf_transformation,[],[f3])).
% 7.53/1.51  
% 7.53/1.51  fof(f58,plain,(
% 7.53/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.53/1.51    inference(flattening,[],[f57])).
% 7.53/1.51  
% 7.53/1.51  fof(f75,plain,(
% 7.53/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f58])).
% 7.53/1.51  
% 7.53/1.51  fof(f101,plain,(
% 7.53/1.51    v1_tdlat_3(sK3)),
% 7.53/1.51    inference(cnf_transformation,[],[f67])).
% 7.53/1.51  
% 7.53/1.51  fof(f8,axiom,(
% 7.53/1.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f23,plain,(
% 7.53/1.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 7.53/1.51    inference(pure_predicate_removal,[],[f8])).
% 7.53/1.51  
% 7.53/1.51  fof(f29,plain,(
% 7.53/1.51    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.53/1.51    inference(ennf_transformation,[],[f23])).
% 7.53/1.51  
% 7.53/1.51  fof(f30,plain,(
% 7.53/1.51    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.53/1.51    inference(flattening,[],[f29])).
% 7.53/1.51  
% 7.53/1.51  fof(f83,plain,(
% 7.53/1.51    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f30])).
% 7.53/1.51  
% 7.53/1.51  fof(f15,axiom,(
% 7.53/1.51    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f39,plain,(
% 7.53/1.51    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 7.53/1.51    inference(ennf_transformation,[],[f15])).
% 7.53/1.51  
% 7.53/1.51  fof(f40,plain,(
% 7.53/1.51    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 7.53/1.51    inference(flattening,[],[f39])).
% 7.53/1.51  
% 7.53/1.51  fof(f91,plain,(
% 7.53/1.51    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f40])).
% 7.53/1.51  
% 7.53/1.51  fof(f16,axiom,(
% 7.53/1.51    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f21,plain,(
% 7.53/1.51    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 7.53/1.51    inference(pure_predicate_removal,[],[f16])).
% 7.53/1.51  
% 7.53/1.51  fof(f22,plain,(
% 7.53/1.51    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v1_tdlat_3(X1)))),
% 7.53/1.51    inference(pure_predicate_removal,[],[f21])).
% 7.53/1.51  
% 7.53/1.51  fof(f41,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.53/1.51    inference(ennf_transformation,[],[f22])).
% 7.53/1.51  
% 7.53/1.51  fof(f42,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.53/1.51    inference(flattening,[],[f41])).
% 7.53/1.51  
% 7.53/1.51  fof(f92,plain,(
% 7.53/1.51    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f42])).
% 7.53/1.51  
% 7.53/1.51  fof(f12,axiom,(
% 7.53/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f35,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.53/1.51    inference(ennf_transformation,[],[f12])).
% 7.53/1.51  
% 7.53/1.51  fof(f87,plain,(
% 7.53/1.51    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f35])).
% 7.53/1.51  
% 7.53/1.51  fof(f17,axiom,(
% 7.53/1.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f43,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.53/1.51    inference(ennf_transformation,[],[f17])).
% 7.53/1.51  
% 7.53/1.51  fof(f44,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.53/1.51    inference(flattening,[],[f43])).
% 7.53/1.51  
% 7.53/1.51  fof(f60,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.53/1.51    inference(nnf_transformation,[],[f44])).
% 7.53/1.51  
% 7.53/1.51  fof(f94,plain,(
% 7.53/1.51    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f60])).
% 7.53/1.51  
% 7.53/1.51  fof(f107,plain,(
% 7.53/1.51    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.53/1.51    inference(equality_resolution,[],[f94])).
% 7.53/1.51  
% 7.53/1.51  fof(f14,axiom,(
% 7.53/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f38,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.53/1.51    inference(ennf_transformation,[],[f14])).
% 7.53/1.51  
% 7.53/1.51  fof(f90,plain,(
% 7.53/1.51    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f38])).
% 7.53/1.51  
% 7.53/1.51  fof(f9,axiom,(
% 7.53/1.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f31,plain,(
% 7.53/1.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.53/1.51    inference(ennf_transformation,[],[f9])).
% 7.53/1.51  
% 7.53/1.51  fof(f84,plain,(
% 7.53/1.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f31])).
% 7.53/1.51  
% 7.53/1.51  fof(f11,axiom,(
% 7.53/1.51    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f33,plain,(
% 7.53/1.51    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 7.53/1.51    inference(ennf_transformation,[],[f11])).
% 7.53/1.51  
% 7.53/1.51  fof(f34,plain,(
% 7.53/1.51    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 7.53/1.51    inference(flattening,[],[f33])).
% 7.53/1.51  
% 7.53/1.51  fof(f86,plain,(
% 7.53/1.51    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f34])).
% 7.53/1.51  
% 7.53/1.51  fof(f10,axiom,(
% 7.53/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f32,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.53/1.51    inference(ennf_transformation,[],[f10])).
% 7.53/1.51  
% 7.53/1.51  fof(f85,plain,(
% 7.53/1.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f32])).
% 7.53/1.51  
% 7.53/1.51  fof(f98,plain,(
% 7.53/1.51    ( ! [X0,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f64])).
% 7.53/1.51  
% 7.53/1.51  fof(f7,axiom,(
% 7.53/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f27,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.53/1.51    inference(ennf_transformation,[],[f7])).
% 7.53/1.51  
% 7.53/1.51  fof(f28,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.53/1.51    inference(flattening,[],[f27])).
% 7.53/1.51  
% 7.53/1.51  fof(f82,plain,(
% 7.53/1.51    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f28])).
% 7.53/1.51  
% 7.53/1.51  fof(f13,axiom,(
% 7.53/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f36,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.53/1.51    inference(ennf_transformation,[],[f13])).
% 7.53/1.51  
% 7.53/1.51  fof(f37,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.53/1.51    inference(flattening,[],[f36])).
% 7.53/1.51  
% 7.53/1.51  fof(f88,plain,(
% 7.53/1.51    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f37])).
% 7.53/1.51  
% 7.53/1.51  fof(f6,axiom,(
% 7.53/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f26,plain,(
% 7.53/1.51    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.53/1.51    inference(ennf_transformation,[],[f6])).
% 7.53/1.51  
% 7.53/1.51  fof(f81,plain,(
% 7.53/1.51    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.53/1.51    inference(cnf_transformation,[],[f26])).
% 7.53/1.51  
% 7.53/1.51  cnf(c_32,negated_conjecture,
% 7.53/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 7.53/1.51      inference(cnf_transformation,[],[f103]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3136,plain,
% 7.53/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_28,plain,
% 7.53/1.51      ( v2_tex_2(X0,X1)
% 7.53/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.53/1.51      | r1_tarski(sK2(X1,X0),X0)
% 7.53/1.51      | v2_struct_0(X1)
% 7.53/1.51      | ~ v2_pre_topc(X1)
% 7.53/1.51      | ~ l1_pre_topc(X1) ),
% 7.53/1.51      inference(cnf_transformation,[],[f97]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3140,plain,
% 7.53/1.51      ( v2_tex_2(X0,X1) = iProver_top
% 7.53/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.53/1.51      | r1_tarski(sK2(X1,X0),X0) = iProver_top
% 7.53/1.51      | v2_struct_0(X1) = iProver_top
% 7.53/1.51      | v2_pre_topc(X1) != iProver_top
% 7.53/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_4945,plain,
% 7.53/1.51      ( v2_tex_2(sK4,sK3) = iProver_top
% 7.53/1.51      | r1_tarski(sK2(sK3,sK4),sK4) = iProver_top
% 7.53/1.51      | v2_struct_0(sK3) = iProver_top
% 7.53/1.51      | v2_pre_topc(sK3) != iProver_top
% 7.53/1.51      | l1_pre_topc(sK3) != iProver_top ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_3136,c_3140]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_36,negated_conjecture,
% 7.53/1.51      ( ~ v2_struct_0(sK3) ),
% 7.53/1.51      inference(cnf_transformation,[],[f99]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_37,plain,
% 7.53/1.51      ( v2_struct_0(sK3) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_35,negated_conjecture,
% 7.53/1.51      ( v2_pre_topc(sK3) ),
% 7.53/1.51      inference(cnf_transformation,[],[f100]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_38,plain,
% 7.53/1.51      ( v2_pre_topc(sK3) = iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_33,negated_conjecture,
% 7.53/1.51      ( l1_pre_topc(sK3) ),
% 7.53/1.51      inference(cnf_transformation,[],[f102]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_40,plain,
% 7.53/1.51      ( l1_pre_topc(sK3) = iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_41,plain,
% 7.53/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_31,negated_conjecture,
% 7.53/1.51      ( ~ v2_tex_2(sK4,sK3) ),
% 7.53/1.51      inference(cnf_transformation,[],[f104]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_1514,plain,
% 7.53/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.53/1.51      | r1_tarski(sK2(X1,X0),X0)
% 7.53/1.51      | v2_struct_0(X1)
% 7.53/1.51      | ~ v2_pre_topc(X1)
% 7.53/1.51      | ~ l1_pre_topc(X1)
% 7.53/1.51      | sK3 != X1
% 7.53/1.51      | sK4 != X0 ),
% 7.53/1.51      inference(resolution_lifted,[status(thm)],[c_28,c_31]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_1515,plain,
% 7.53/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.53/1.51      | r1_tarski(sK2(sK3,sK4),sK4)
% 7.53/1.51      | v2_struct_0(sK3)
% 7.53/1.51      | ~ v2_pre_topc(sK3)
% 7.53/1.51      | ~ l1_pre_topc(sK3) ),
% 7.53/1.51      inference(unflattening,[status(thm)],[c_1514]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_1516,plain,
% 7.53/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.53/1.51      | r1_tarski(sK2(sK3,sK4),sK4) = iProver_top
% 7.53/1.51      | v2_struct_0(sK3) = iProver_top
% 7.53/1.51      | v2_pre_topc(sK3) != iProver_top
% 7.53/1.51      | l1_pre_topc(sK3) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_1515]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_5609,plain,
% 7.53/1.51      ( r1_tarski(sK2(sK3,sK4),sK4) = iProver_top ),
% 7.53/1.51      inference(global_propositional_subsumption,
% 7.53/1.51                [status(thm)],
% 7.53/1.51                [c_4945,c_37,c_38,c_40,c_41,c_1516]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3,plain,
% 7.53/1.51      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.53/1.51      inference(cnf_transformation,[],[f71]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3155,plain,
% 7.53/1.51      ( r1_tarski(X0,X1) = iProver_top
% 7.53/1.51      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_1,plain,
% 7.53/1.51      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.53/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3157,plain,
% 7.53/1.51      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3609,plain,
% 7.53/1.51      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_3155,c_3157]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_5,plain,
% 7.53/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.53/1.51      inference(cnf_transformation,[],[f75]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3153,plain,
% 7.53/1.51      ( X0 = X1
% 7.53/1.51      | r1_tarski(X1,X0) != iProver_top
% 7.53/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_4349,plain,
% 7.53/1.51      ( X0 = X1
% 7.53/1.51      | r1_tarski(X0,X1) != iProver_top
% 7.53/1.51      | v1_xboole_0(X1) != iProver_top ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_3609,c_3153]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_5615,plain,
% 7.53/1.51      ( sK2(sK3,sK4) = sK4 | v1_xboole_0(sK4) != iProver_top ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_5609,c_4349]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_34,negated_conjecture,
% 7.53/1.51      ( v1_tdlat_3(sK3) ),
% 7.53/1.51      inference(cnf_transformation,[],[f101]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_39,plain,
% 7.53/1.51      ( v1_tdlat_3(sK3) = iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_42,plain,
% 7.53/1.51      ( v2_tex_2(sK4,sK3) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_15,plain,
% 7.53/1.51      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 7.53/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.53/1.51      | ~ l1_pre_topc(X0) ),
% 7.53/1.51      inference(cnf_transformation,[],[f83]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3470,plain,
% 7.53/1.51      ( m1_pre_topc(k1_pre_topc(sK3,sK4),sK3)
% 7.53/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.53/1.51      | ~ l1_pre_topc(sK3) ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3471,plain,
% 7.53/1.51      ( m1_pre_topc(k1_pre_topc(sK3,sK4),sK3) = iProver_top
% 7.53/1.51      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.53/1.51      | l1_pre_topc(sK3) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_3470]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_23,plain,
% 7.53/1.51      ( ~ v1_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 7.53/1.51      inference(cnf_transformation,[],[f91]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_24,plain,
% 7.53/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.53/1.51      | ~ v1_tdlat_3(X1)
% 7.53/1.51      | v1_tdlat_3(X0)
% 7.53/1.51      | v2_struct_0(X1)
% 7.53/1.51      | ~ v2_pre_topc(X1)
% 7.53/1.51      | ~ l1_pre_topc(X1) ),
% 7.53/1.51      inference(cnf_transformation,[],[f92]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_704,plain,
% 7.53/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.53/1.51      | ~ v1_tdlat_3(X2)
% 7.53/1.51      | ~ v1_tdlat_3(X1)
% 7.53/1.51      | v1_tdlat_3(X0)
% 7.53/1.51      | v2_struct_0(X1)
% 7.53/1.51      | ~ l1_pre_topc(X2)
% 7.53/1.51      | ~ l1_pre_topc(X1)
% 7.53/1.51      | X1 != X2 ),
% 7.53/1.51      inference(resolution_lifted,[status(thm)],[c_23,c_24]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_705,plain,
% 7.53/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.53/1.51      | ~ v1_tdlat_3(X1)
% 7.53/1.51      | v1_tdlat_3(X0)
% 7.53/1.51      | v2_struct_0(X1)
% 7.53/1.51      | ~ l1_pre_topc(X1) ),
% 7.53/1.51      inference(unflattening,[status(thm)],[c_704]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3647,plain,
% 7.53/1.51      ( ~ m1_pre_topc(k1_pre_topc(sK3,sK4),X0)
% 7.53/1.51      | ~ v1_tdlat_3(X0)
% 7.53/1.51      | v1_tdlat_3(k1_pre_topc(sK3,sK4))
% 7.53/1.51      | v2_struct_0(X0)
% 7.53/1.51      | ~ l1_pre_topc(X0) ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_705]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3648,plain,
% 7.53/1.51      ( m1_pre_topc(k1_pre_topc(sK3,sK4),X0) != iProver_top
% 7.53/1.51      | v1_tdlat_3(X0) != iProver_top
% 7.53/1.51      | v1_tdlat_3(k1_pre_topc(sK3,sK4)) = iProver_top
% 7.53/1.51      | v2_struct_0(X0) = iProver_top
% 7.53/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_3647]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3650,plain,
% 7.53/1.51      ( m1_pre_topc(k1_pre_topc(sK3,sK4),sK3) != iProver_top
% 7.53/1.51      | v1_tdlat_3(k1_pre_topc(sK3,sK4)) = iProver_top
% 7.53/1.51      | v1_tdlat_3(sK3) != iProver_top
% 7.53/1.51      | v2_struct_0(sK3) = iProver_top
% 7.53/1.51      | l1_pre_topc(sK3) != iProver_top ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_3648]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19,plain,
% 7.53/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.53/1.51      | ~ l1_pre_topc(X1)
% 7.53/1.51      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 7.53/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3144,plain,
% 7.53/1.51      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
% 7.53/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.53/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_4757,plain,
% 7.53/1.51      ( u1_struct_0(k1_pre_topc(sK3,sK4)) = sK4
% 7.53/1.51      | l1_pre_topc(sK3) != iProver_top ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_3136,c_3144]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3475,plain,
% 7.53/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.53/1.51      | ~ l1_pre_topc(sK3)
% 7.53/1.51      | u1_struct_0(k1_pre_topc(sK3,sK4)) = sK4 ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_19]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_5350,plain,
% 7.53/1.51      ( u1_struct_0(k1_pre_topc(sK3,sK4)) = sK4 ),
% 7.53/1.51      inference(global_propositional_subsumption,
% 7.53/1.51                [status(thm)],
% 7.53/1.51                [c_4757,c_33,c_32,c_3475]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_25,plain,
% 7.53/1.51      ( v2_tex_2(u1_struct_0(X0),X1)
% 7.53/1.51      | ~ m1_pre_topc(X0,X1)
% 7.53/1.51      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.53/1.51      | ~ v1_tdlat_3(X0)
% 7.53/1.51      | v2_struct_0(X1)
% 7.53/1.51      | v2_struct_0(X0)
% 7.53/1.51      | ~ l1_pre_topc(X1) ),
% 7.53/1.51      inference(cnf_transformation,[],[f107]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_22,plain,
% 7.53/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.53/1.51      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.53/1.51      | ~ l1_pre_topc(X1) ),
% 7.53/1.51      inference(cnf_transformation,[],[f90]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_206,plain,
% 7.53/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.53/1.51      | v2_tex_2(u1_struct_0(X0),X1)
% 7.53/1.51      | ~ v1_tdlat_3(X0)
% 7.53/1.51      | v2_struct_0(X1)
% 7.53/1.51      | v2_struct_0(X0)
% 7.53/1.51      | ~ l1_pre_topc(X1) ),
% 7.53/1.51      inference(global_propositional_subsumption,[status(thm)],[c_25,c_22]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_207,plain,
% 7.53/1.51      ( v2_tex_2(u1_struct_0(X0),X1)
% 7.53/1.51      | ~ m1_pre_topc(X0,X1)
% 7.53/1.51      | ~ v1_tdlat_3(X0)
% 7.53/1.51      | v2_struct_0(X0)
% 7.53/1.51      | v2_struct_0(X1)
% 7.53/1.51      | ~ l1_pre_topc(X1) ),
% 7.53/1.51      inference(renaming,[status(thm)],[c_206]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3130,plain,
% 7.53/1.51      ( v2_tex_2(u1_struct_0(X0),X1) = iProver_top
% 7.53/1.51      | m1_pre_topc(X0,X1) != iProver_top
% 7.53/1.51      | v1_tdlat_3(X0) != iProver_top
% 7.53/1.51      | v2_struct_0(X1) = iProver_top
% 7.53/1.51      | v2_struct_0(X0) = iProver_top
% 7.53/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_207]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_5355,plain,
% 7.53/1.51      ( v2_tex_2(sK4,X0) = iProver_top
% 7.53/1.51      | m1_pre_topc(k1_pre_topc(sK3,sK4),X0) != iProver_top
% 7.53/1.51      | v1_tdlat_3(k1_pre_topc(sK3,sK4)) != iProver_top
% 7.53/1.51      | v2_struct_0(X0) = iProver_top
% 7.53/1.51      | v2_struct_0(k1_pre_topc(sK3,sK4)) = iProver_top
% 7.53/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_5350,c_3130]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_5457,plain,
% 7.53/1.51      ( v2_tex_2(sK4,sK3) = iProver_top
% 7.53/1.51      | m1_pre_topc(k1_pre_topc(sK3,sK4),sK3) != iProver_top
% 7.53/1.51      | v1_tdlat_3(k1_pre_topc(sK3,sK4)) != iProver_top
% 7.53/1.51      | v2_struct_0(k1_pre_topc(sK3,sK4)) = iProver_top
% 7.53/1.51      | v2_struct_0(sK3) = iProver_top
% 7.53/1.51      | l1_pre_topc(sK3) != iProver_top ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_5355]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_16,plain,
% 7.53/1.51      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.53/1.51      inference(cnf_transformation,[],[f84]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_18,plain,
% 7.53/1.51      ( ~ v2_struct_0(X0) | ~ l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0)) ),
% 7.53/1.51      inference(cnf_transformation,[],[f86]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_411,plain,
% 7.53/1.51      ( ~ v2_struct_0(X0) | ~ l1_pre_topc(X0) | v1_xboole_0(u1_struct_0(X0)) ),
% 7.53/1.51      inference(resolution,[status(thm)],[c_16,c_18]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3128,plain,
% 7.53/1.51      ( v2_struct_0(X0) != iProver_top
% 7.53/1.51      | l1_pre_topc(X0) != iProver_top
% 7.53/1.51      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_411]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_5359,plain,
% 7.53/1.51      ( v2_struct_0(k1_pre_topc(sK3,sK4)) != iProver_top
% 7.53/1.51      | l1_pre_topc(k1_pre_topc(sK3,sK4)) != iProver_top
% 7.53/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_5350,c_3128]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3146,plain,
% 7.53/1.51      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 7.53/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.53/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_4917,plain,
% 7.53/1.51      ( m1_pre_topc(k1_pre_topc(sK3,sK4),sK3) = iProver_top
% 7.53/1.51      | l1_pre_topc(sK3) != iProver_top ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_3136,c_3146]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_5480,plain,
% 7.53/1.51      ( m1_pre_topc(k1_pre_topc(sK3,sK4),sK3) = iProver_top ),
% 7.53/1.51      inference(global_propositional_subsumption,
% 7.53/1.51                [status(thm)],
% 7.53/1.51                [c_4917,c_40,c_41,c_3471]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_17,plain,
% 7.53/1.51      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.53/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3145,plain,
% 7.53/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.53/1.51      | l1_pre_topc(X1) != iProver_top
% 7.53/1.51      | l1_pre_topc(X0) = iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_5486,plain,
% 7.53/1.51      ( l1_pre_topc(k1_pre_topc(sK3,sK4)) = iProver_top
% 7.53/1.51      | l1_pre_topc(sK3) != iProver_top ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_5480,c_3145]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_5635,plain,
% 7.53/1.51      ( sK2(sK3,sK4) = sK4 ),
% 7.53/1.51      inference(global_propositional_subsumption,
% 7.53/1.51                [status(thm)],
% 7.53/1.51                [c_5615,c_37,c_39,c_40,c_41,c_42,c_3471,c_3650,c_5457,c_5359,
% 7.53/1.51                 c_5486]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_27,plain,
% 7.53/1.51      ( v2_tex_2(X0,X1)
% 7.53/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.53/1.51      | v2_struct_0(X1)
% 7.53/1.51      | ~ v2_pre_topc(X1)
% 7.53/1.51      | ~ l1_pre_topc(X1)
% 7.53/1.51      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,sK2(X1,X0))) != sK2(X1,X0) ),
% 7.53/1.51      inference(cnf_transformation,[],[f98]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3141,plain,
% 7.53/1.51      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
% 7.53/1.51      | v2_tex_2(X1,X0) = iProver_top
% 7.53/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.53/1.51      | v2_struct_0(X0) = iProver_top
% 7.53/1.51      | v2_pre_topc(X0) != iProver_top
% 7.53/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_5640,plain,
% 7.53/1.51      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK4)) != sK2(sK3,sK4)
% 7.53/1.51      | v2_tex_2(sK4,sK3) = iProver_top
% 7.53/1.51      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.53/1.51      | v2_struct_0(sK3) = iProver_top
% 7.53/1.51      | v2_pre_topc(sK3) != iProver_top
% 7.53/1.51      | l1_pre_topc(sK3) != iProver_top ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_5635,c_3141]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_5647,plain,
% 7.53/1.51      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK4)) != sK4
% 7.53/1.51      | v2_tex_2(sK4,sK3) = iProver_top
% 7.53/1.51      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.53/1.51      | v2_struct_0(sK3) = iProver_top
% 7.53/1.51      | v2_pre_topc(sK3) != iProver_top
% 7.53/1.51      | l1_pre_topc(sK3) != iProver_top ),
% 7.53/1.51      inference(light_normalisation,[status(thm)],[c_5640,c_5635]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_18882,plain,
% 7.53/1.51      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK4)) != sK4 ),
% 7.53/1.51      inference(global_propositional_subsumption,
% 7.53/1.51                [status(thm)],
% 7.53/1.51                [c_5647,c_37,c_38,c_40,c_41,c_42]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_6143,plain,
% 7.53/1.51      ( v1_xboole_0(sK4) = iProver_top ),
% 7.53/1.51      inference(global_propositional_subsumption,
% 7.53/1.51                [status(thm)],
% 7.53/1.51                [c_5359,c_37,c_39,c_40,c_41,c_42,c_3471,c_3650,c_5457,c_5486]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_14,plain,
% 7.53/1.51      ( v4_pre_topc(X0,X1)
% 7.53/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.53/1.51      | ~ v2_pre_topc(X1)
% 7.53/1.51      | ~ l1_pre_topc(X1)
% 7.53/1.51      | ~ v1_xboole_0(X0) ),
% 7.53/1.51      inference(cnf_transformation,[],[f82]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_21,plain,
% 7.53/1.51      ( ~ v4_pre_topc(X0,X1)
% 7.53/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.53/1.51      | ~ l1_pre_topc(X1)
% 7.53/1.51      | k2_pre_topc(X1,X0) = X0 ),
% 7.53/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_428,plain,
% 7.53/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.53/1.51      | ~ v2_pre_topc(X1)
% 7.53/1.51      | ~ l1_pre_topc(X1)
% 7.53/1.51      | ~ v1_xboole_0(X0)
% 7.53/1.51      | k2_pre_topc(X1,X0) = X0 ),
% 7.53/1.51      inference(resolution,[status(thm)],[c_14,c_21]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3127,plain,
% 7.53/1.51      ( k2_pre_topc(X0,X1) = X1
% 7.53/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.53/1.51      | v2_pre_topc(X0) != iProver_top
% 7.53/1.51      | l1_pre_topc(X0) != iProver_top
% 7.53/1.51      | v1_xboole_0(X1) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_4154,plain,
% 7.53/1.51      ( k2_pre_topc(sK3,sK4) = sK4
% 7.53/1.51      | v2_pre_topc(sK3) != iProver_top
% 7.53/1.51      | l1_pre_topc(sK3) != iProver_top
% 7.53/1.51      | v1_xboole_0(sK4) != iProver_top ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_3136,c_3127]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_4359,plain,
% 7.53/1.51      ( k2_pre_topc(sK3,sK4) = sK4 | v1_xboole_0(sK4) != iProver_top ),
% 7.53/1.51      inference(global_propositional_subsumption,
% 7.53/1.51                [status(thm)],
% 7.53/1.51                [c_4154,c_38,c_40]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_6149,plain,
% 7.53/1.51      ( k2_pre_topc(sK3,sK4) = sK4 ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_6143,c_4359]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_18884,plain,
% 7.53/1.51      ( k9_subset_1(u1_struct_0(sK3),sK4,sK4) != sK4 ),
% 7.53/1.51      inference(light_normalisation,[status(thm)],[c_18882,c_6149]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_13,plain,
% 7.53/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k9_subset_1(X1,X2,X2) = X2 ),
% 7.53/1.51      inference(cnf_transformation,[],[f81]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3147,plain,
% 7.53/1.51      ( k9_subset_1(X0,X1,X1) = X1
% 7.53/1.51      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3716,plain,
% 7.53/1.51      ( k9_subset_1(u1_struct_0(sK3),X0,X0) = X0 ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_3136,c_3147]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_18885,plain,
% 7.53/1.51      ( sK4 != sK4 ),
% 7.53/1.51      inference(demodulation,[status(thm)],[c_18884,c_3716]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_18886,plain,
% 7.53/1.51      ( $false ),
% 7.53/1.51      inference(equality_resolution_simp,[status(thm)],[c_18885]) ).
% 7.53/1.51  
% 7.53/1.51  
% 7.53/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.53/1.51  
% 7.53/1.51  ------                               Statistics
% 7.53/1.51  
% 7.53/1.51  ------ General
% 7.53/1.51  
% 7.53/1.51  abstr_ref_over_cycles:                  0
% 7.53/1.51  abstr_ref_under_cycles:                 0
% 7.53/1.51  gc_basic_clause_elim:                   0
% 7.53/1.51  forced_gc_time:                         0
% 7.53/1.51  parsing_time:                           0.011
% 7.53/1.51  unif_index_cands_time:                  0.
% 7.53/1.51  unif_index_add_time:                    0.
% 7.53/1.51  orderings_time:                         0.
% 7.53/1.51  out_proof_time:                         0.01
% 7.53/1.51  total_time:                             0.679
% 7.53/1.51  num_of_symbols:                         53
% 7.53/1.51  num_of_terms:                           12876
% 7.53/1.51  
% 7.53/1.51  ------ Preprocessing
% 7.53/1.51  
% 7.53/1.51  num_of_splits:                          0
% 7.53/1.51  num_of_split_atoms:                     0
% 7.53/1.51  num_of_reused_defs:                     0
% 7.53/1.51  num_eq_ax_congr_red:                    39
% 7.53/1.51  num_of_sem_filtered_clauses:            1
% 7.53/1.51  num_of_subtypes:                        0
% 7.53/1.51  monotx_restored_types:                  0
% 7.53/1.51  sat_num_of_epr_types:                   0
% 7.53/1.51  sat_num_of_non_cyclic_types:            0
% 7.53/1.51  sat_guarded_non_collapsed_types:        0
% 7.53/1.51  num_pure_diseq_elim:                    0
% 7.53/1.51  simp_replaced_by:                       0
% 7.53/1.51  res_preprocessed:                       168
% 7.53/1.51  prep_upred:                             0
% 7.53/1.51  prep_unflattend:                        92
% 7.53/1.51  smt_new_axioms:                         0
% 7.53/1.51  pred_elim_cands:                        10
% 7.53/1.51  pred_elim:                              2
% 7.53/1.51  pred_elim_cl:                           3
% 7.53/1.51  pred_elim_cycles:                       10
% 7.53/1.51  merged_defs:                            0
% 7.53/1.51  merged_defs_ncl:                        0
% 7.53/1.51  bin_hyper_res:                          0
% 7.53/1.51  prep_cycles:                            4
% 7.53/1.51  pred_elim_time:                         0.046
% 7.53/1.51  splitting_time:                         0.
% 7.53/1.51  sem_filter_time:                        0.
% 7.53/1.51  monotx_time:                            0.001
% 7.53/1.51  subtype_inf_time:                       0.
% 7.53/1.51  
% 7.53/1.51  ------ Problem properties
% 7.53/1.51  
% 7.53/1.51  clauses:                                33
% 7.53/1.51  conjectures:                            6
% 7.53/1.51  epr:                                    16
% 7.53/1.51  horn:                                   23
% 7.53/1.51  ground:                                 6
% 7.53/1.51  unary:                                  8
% 7.53/1.51  binary:                                 6
% 7.53/1.51  lits:                                   101
% 7.53/1.51  lits_eq:                                6
% 7.53/1.51  fd_pure:                                0
% 7.53/1.51  fd_pseudo:                              0
% 7.53/1.51  fd_cond:                                0
% 7.53/1.51  fd_pseudo_cond:                         1
% 7.53/1.51  ac_symbols:                             0
% 7.53/1.51  
% 7.53/1.51  ------ Propositional Solver
% 7.53/1.51  
% 7.53/1.51  prop_solver_calls:                      28
% 7.53/1.51  prop_fast_solver_calls:                 2282
% 7.53/1.51  smt_solver_calls:                       0
% 7.53/1.51  smt_fast_solver_calls:                  0
% 7.53/1.51  prop_num_of_clauses:                    6402
% 7.53/1.51  prop_preprocess_simplified:             12983
% 7.53/1.51  prop_fo_subsumed:                       183
% 7.53/1.51  prop_solver_time:                       0.
% 7.53/1.51  smt_solver_time:                        0.
% 7.53/1.51  smt_fast_solver_time:                   0.
% 7.53/1.51  prop_fast_solver_time:                  0.
% 7.53/1.51  prop_unsat_core_time:                   0.
% 7.53/1.51  
% 7.53/1.51  ------ QBF
% 7.53/1.51  
% 7.53/1.51  qbf_q_res:                              0
% 7.53/1.51  qbf_num_tautologies:                    0
% 7.53/1.51  qbf_prep_cycles:                        0
% 7.53/1.51  
% 7.53/1.51  ------ BMC1
% 7.53/1.51  
% 7.53/1.51  bmc1_current_bound:                     -1
% 7.53/1.51  bmc1_last_solved_bound:                 -1
% 7.53/1.51  bmc1_unsat_core_size:                   -1
% 7.53/1.51  bmc1_unsat_core_parents_size:           -1
% 7.53/1.51  bmc1_merge_next_fun:                    0
% 7.53/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.53/1.51  
% 7.53/1.51  ------ Instantiation
% 7.53/1.51  
% 7.53/1.51  inst_num_of_clauses:                    1565
% 7.53/1.51  inst_num_in_passive:                    191
% 7.53/1.51  inst_num_in_active:                     641
% 7.53/1.51  inst_num_in_unprocessed:                735
% 7.53/1.51  inst_num_of_loops:                      810
% 7.53/1.51  inst_num_of_learning_restarts:          0
% 7.53/1.51  inst_num_moves_active_passive:          166
% 7.53/1.51  inst_lit_activity:                      0
% 7.53/1.51  inst_lit_activity_moves:                0
% 7.53/1.51  inst_num_tautologies:                   0
% 7.53/1.51  inst_num_prop_implied:                  0
% 7.53/1.51  inst_num_existing_simplified:           0
% 7.53/1.51  inst_num_eq_res_simplified:             0
% 7.53/1.51  inst_num_child_elim:                    0
% 7.53/1.51  inst_num_of_dismatching_blockings:      359
% 7.53/1.51  inst_num_of_non_proper_insts:           1260
% 7.53/1.51  inst_num_of_duplicates:                 0
% 7.53/1.51  inst_inst_num_from_inst_to_res:         0
% 7.53/1.51  inst_dismatching_checking_time:         0.
% 7.53/1.51  
% 7.53/1.51  ------ Resolution
% 7.53/1.51  
% 7.53/1.51  res_num_of_clauses:                     0
% 7.53/1.51  res_num_in_passive:                     0
% 7.53/1.51  res_num_in_active:                      0
% 7.53/1.51  res_num_of_loops:                       172
% 7.53/1.51  res_forward_subset_subsumed:            100
% 7.53/1.51  res_backward_subset_subsumed:           12
% 7.53/1.51  res_forward_subsumed:                   0
% 7.53/1.51  res_backward_subsumed:                  1
% 7.53/1.51  res_forward_subsumption_resolution:     1
% 7.53/1.51  res_backward_subsumption_resolution:    0
% 7.53/1.51  res_clause_to_clause_subsumption:       1329
% 7.53/1.51  res_orphan_elimination:                 0
% 7.53/1.51  res_tautology_del:                      99
% 7.53/1.51  res_num_eq_res_simplified:              0
% 7.53/1.51  res_num_sel_changes:                    0
% 7.53/1.51  res_moves_from_active_to_pass:          0
% 7.53/1.51  
% 7.53/1.51  ------ Superposition
% 7.53/1.51  
% 7.53/1.51  sup_time_total:                         0.
% 7.53/1.51  sup_time_generating:                    0.
% 7.53/1.51  sup_time_sim_full:                      0.
% 7.53/1.51  sup_time_sim_immed:                     0.
% 7.53/1.51  
% 7.53/1.51  sup_num_of_clauses:                     452
% 7.53/1.51  sup_num_in_active:                      157
% 7.53/1.51  sup_num_in_passive:                     295
% 7.53/1.51  sup_num_of_loops:                       161
% 7.53/1.51  sup_fw_superposition:                   214
% 7.53/1.51  sup_bw_superposition:                   372
% 7.53/1.51  sup_immediate_simplified:               209
% 7.53/1.51  sup_given_eliminated:                   0
% 7.53/1.51  comparisons_done:                       0
% 7.53/1.51  comparisons_avoided:                    6
% 7.53/1.51  
% 7.53/1.51  ------ Simplifications
% 7.53/1.51  
% 7.53/1.51  
% 7.53/1.51  sim_fw_subset_subsumed:                 34
% 7.53/1.51  sim_bw_subset_subsumed:                 14
% 7.53/1.51  sim_fw_subsumed:                        49
% 7.53/1.51  sim_bw_subsumed:                        0
% 7.53/1.51  sim_fw_subsumption_res:                 6
% 7.53/1.51  sim_bw_subsumption_res:                 0
% 7.53/1.51  sim_tautology_del:                      12
% 7.53/1.51  sim_eq_tautology_del:                   13
% 7.53/1.51  sim_eq_res_simp:                        0
% 7.53/1.51  sim_fw_demodulated:                     2
% 7.53/1.51  sim_bw_demodulated:                     2
% 7.53/1.51  sim_light_normalised:                   132
% 7.53/1.51  sim_joinable_taut:                      0
% 7.53/1.51  sim_joinable_simp:                      0
% 7.53/1.51  sim_ac_normalised:                      0
% 7.53/1.51  sim_smt_subsumption:                    0
% 7.53/1.51  
%------------------------------------------------------------------------------
