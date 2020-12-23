%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:41 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  207 (1310 expanded)
%              Number of clauses        :  127 ( 426 expanded)
%              Number of leaves         :   23 ( 309 expanded)
%              Depth                    :   23
%              Number of atoms          :  703 (5855 expanded)
%              Number of equality atoms :  171 ( 556 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v1_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ~ v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v1_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f43,f56,f55])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK1(X0,X1)) = X1
        & m1_pre_topc(sK1(X0,X1),X0)
        & ~ v2_struct_0(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK1(X0,X1)) = X1
            & m1_pre_topc(sK1(X0,X1),X0)
            & ~ v2_struct_0(sK1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f51])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f90,plain,(
    ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f15,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f13,axiom,(
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
    inference(pure_predicate_removal,[],[f13])).

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

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ( ~ v2_tex_2(X2,X0)
                & ~ v2_tex_2(X1,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ( ~ v2_tex_2(X2,X0)
                & ~ v2_tex_2(X1,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_tdlat_3(X0) )
            & ( v1_tdlat_3(X0)
              | ~ v2_tex_2(X1,X0) ) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_tdlat_3(X0)
      | u1_struct_0(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f95,plain,(
    ! [X0] :
      ( v2_tex_2(u1_struct_0(X0),X0)
      | ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1735,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_767,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_768,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,X0),X0) ),
    inference(unflattening,[status(thm)],[c_767])).

cnf(c_1724,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k1_tops_1(sK2,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_2023,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1735,c_1724])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_241,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_242,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_241])).

cnf(c_296,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_242])).

cnf(c_1733,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_296])).

cnf(c_4036,plain,
    ( k9_subset_1(sK3,X0,k1_tops_1(sK2,sK3)) = k3_xboole_0(X0,k1_tops_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_2023,c_1733])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_295,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_242])).

cnf(c_1734,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_295])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1737,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2721,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_1737])).

cnf(c_4574,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),sK3) != iProver_top
    | r1_tarski(k3_xboole_0(X0,k1_tops_1(sK2,sK3)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4036,c_2721])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1926,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_768])).

cnf(c_1927,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k1_tops_1(sK2,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1926])).

cnf(c_10008,plain,
    ( r1_tarski(k3_xboole_0(X0,k1_tops_1(sK2,sK3)),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4574,c_37,c_1927])).

cnf(c_19,plain,
    ( m1_pre_topc(sK1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_623,plain,
    ( m1_pre_topc(sK1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v1_xboole_0(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_624,plain,
    ( m1_pre_topc(sK1(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_628,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_pre_topc(sK1(sK2,X0),sK2)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_624,c_32])).

cnf(c_629,plain,
    ( m1_pre_topc(sK1(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_628])).

cnf(c_1729,plain,
    ( m1_pre_topc(sK1(sK2,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_2395,plain,
    ( m1_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1735,c_1729])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_755,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_756,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_755])).

cnf(c_1725,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_756])).

cnf(c_2347,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1725,c_1737])).

cnf(c_4035,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(X1)) = k3_xboole_0(X0,u1_struct_0(X1))
    | m1_pre_topc(X1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2347,c_1733])).

cnf(c_9750,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK1(sK2,sK3))) = k3_xboole_0(X0,u1_struct_0(sK1(sK2,sK3)))
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2395,c_4035])).

cnf(c_27,negated_conjecture,
    ( ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_38,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_87,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_91,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_734,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_735,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_734])).

cnf(c_739,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_735,c_32])).

cnf(c_1929,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK3)
    | u1_struct_0(sK1(sK2,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_739])).

cnf(c_1930,plain,
    ( u1_struct_0(sK1(sK2,sK3)) = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1929])).

cnf(c_21,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_176,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_tex_2(u1_struct_0(X0),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_15])).

cnf(c_177,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_176])).

cnf(c_651,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_177,c_29])).

cnf(c_652,plain,
    ( v2_tex_2(u1_struct_0(X0),sK2)
    | ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ v1_tdlat_3(X0) ),
    inference(unflattening,[status(thm)],[c_651])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | v1_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_434,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_31])).

cnf(c_435,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(sK2)
    | v1_tdlat_3(X0)
    | ~ v1_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_30,negated_conjecture,
    ( v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_437,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | v1_tdlat_3(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_435,c_32,c_30,c_29])).

cnf(c_656,plain,
    ( v2_tex_2(u1_struct_0(X0),sK2)
    | ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_652,c_32,c_30,c_29,c_435])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_713,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0))
    | v1_xboole_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_714,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_struct_0(sK1(sK2,X0))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_713])).

cnf(c_718,plain,
    ( ~ v2_struct_0(sK1(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_714,c_32])).

cnf(c_719,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_struct_0(sK1(sK2,X0))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_718])).

cnf(c_824,plain,
    ( v2_tex_2(u1_struct_0(X0),sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X1)
    | sK1(sK2,X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_656,c_719])).

cnf(c_825,plain,
    ( v2_tex_2(u1_struct_0(sK1(sK2,X0)),sK2)
    | ~ m1_pre_topc(sK1(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_824])).

cnf(c_829,plain,
    ( v2_tex_2(u1_struct_0(sK1(sK2,X0)),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_825,c_32,c_624])).

cnf(c_1954,plain,
    ( v2_tex_2(u1_struct_0(sK1(sK2,sK3)),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_829])).

cnf(c_1955,plain,
    ( v2_tex_2(u1_struct_0(sK1(sK2,sK3)),sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1954])).

cnf(c_1141,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2672,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK1(sK2,sK3))
    | u1_struct_0(sK1(sK2,sK3)) != X1 ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_3642,plain,
    ( X0 = u1_struct_0(sK1(sK2,sK3))
    | X0 != sK3
    | u1_struct_0(sK1(sK2,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_2672])).

cnf(c_4983,plain,
    ( u1_struct_0(sK1(sK2,sK3)) != sK3
    | sK3 = u1_struct_0(sK1(sK2,sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3642])).

cnf(c_1140,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4984,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_1151,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2273,plain,
    ( v2_tex_2(X0,X1)
    | ~ v2_tex_2(u1_struct_0(sK1(sK2,sK3)),sK2)
    | X0 != u1_struct_0(sK1(sK2,sK3))
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_1151])).

cnf(c_9735,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1(sK2,sK3)),sK2)
    | v2_tex_2(sK3,X0)
    | X0 != sK2
    | sK3 != u1_struct_0(sK1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2273])).

cnf(c_9736,plain,
    ( X0 != sK2
    | sK3 != u1_struct_0(sK1(sK2,sK3))
    | v2_tex_2(u1_struct_0(sK1(sK2,sK3)),sK2) != iProver_top
    | v2_tex_2(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9735])).

cnf(c_9738,plain,
    ( sK2 != sK2
    | sK3 != u1_struct_0(sK1(sK2,sK3))
    | v2_tex_2(u1_struct_0(sK1(sK2,sK3)),sK2) != iProver_top
    | v2_tex_2(sK3,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_9736])).

cnf(c_9804,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9750,c_37,c_38,c_87,c_91,c_1930,c_1955,c_4983,c_4984,c_9738])).

cnf(c_1740,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1743,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_300,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_242])).

cnf(c_1731,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(c_5827,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1743,c_1731])).

cnf(c_7155,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1740,c_5827])).

cnf(c_1741,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3147,plain,
    ( k1_tops_1(sK2,sK3) = sK3
    | r1_tarski(sK3,k1_tops_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2023,c_1741])).

cnf(c_7409,plain,
    ( k1_tops_1(sK2,sK3) = sK3
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7155,c_3147])).

cnf(c_9809,plain,
    ( k1_tops_1(sK2,sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_9804,c_7409])).

cnf(c_10014,plain,
    ( r1_tarski(k3_xboole_0(X0,sK3),sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10008,c_9809])).

cnf(c_10022,plain,
    ( k3_xboole_0(X0,sK3) = sK3
    | r1_tarski(sK3,k3_xboole_0(X0,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10014,c_1741])).

cnf(c_7404,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7155,c_1741])).

cnf(c_10019,plain,
    ( k3_xboole_0(X0,sK3) = sK3
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10014,c_7404])).

cnf(c_10704,plain,
    ( k3_xboole_0(X0,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10022,c_37,c_38,c_87,c_91,c_1930,c_1955,c_4983,c_4984,c_9738,c_10019])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1739,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1753,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1739,c_6])).

cnf(c_2346,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1735,c_1737])).

cnf(c_4033,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,sK3) = k3_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_2346,c_1733])).

cnf(c_26,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(k9_subset_1(u1_struct_0(X1),X0,X2),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_679,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(k9_subset_1(u1_struct_0(X1),X0,X2),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_29])).

cnf(c_680,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(k9_subset_1(u1_struct_0(sK2),X0,X1),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_1728,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(k9_subset_1(u1_struct_0(sK2),X0,X1),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_4367,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(k3_xboole_0(X0,sK3),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4033,c_1728])).

cnf(c_4591,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_tex_2(k3_xboole_0(X0,sK3),sK2) = iProver_top
    | v2_tex_2(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4367,c_37])).

cnf(c_4592,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(k3_xboole_0(X0,sK3),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4591])).

cnf(c_4604,plain,
    ( v2_tex_2(k3_xboole_0(u1_struct_0(sK2),sK3),sK2) = iProver_top
    | v2_tex_2(u1_struct_0(sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1753,c_4592])).

cnf(c_23,plain,
    ( v2_tex_2(u1_struct_0(X0),X0)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_609,plain,
    ( v2_tex_2(u1_struct_0(X0),X0)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_610,plain,
    ( v2_tex_2(u1_struct_0(sK2),sK2)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v1_tdlat_3(sK2) ),
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_612,plain,
    ( v2_tex_2(u1_struct_0(sK2),sK2)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_610,c_32,c_30])).

cnf(c_1730,plain,
    ( v2_tex_2(u1_struct_0(sK2),sK2) = iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_1790,plain,
    ( v2_tex_2(u1_struct_0(sK2),sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1730,c_1753])).

cnf(c_5359,plain,
    ( v2_tex_2(k3_xboole_0(u1_struct_0(sK2),sK3),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4604,c_1790])).

cnf(c_10723,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10704,c_5359])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10723,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:02:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.55/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/0.98  
% 3.55/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.55/0.98  
% 3.55/0.98  ------  iProver source info
% 3.55/0.98  
% 3.55/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.55/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.55/0.98  git: non_committed_changes: false
% 3.55/0.98  git: last_make_outside_of_git: false
% 3.55/0.98  
% 3.55/0.98  ------ 
% 3.55/0.98  ------ Parsing...
% 3.55/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.55/0.98  
% 3.55/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.55/0.98  
% 3.55/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.55/0.98  
% 3.55/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.55/0.98  ------ Proving...
% 3.55/0.98  ------ Problem Properties 
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  clauses                                 24
% 3.55/0.98  conjectures                             2
% 3.55/0.98  EPR                                     6
% 3.55/0.98  Horn                                    20
% 3.55/0.98  unary                                   5
% 3.55/0.98  binary                                  10
% 3.55/0.98  lits                                    54
% 3.55/0.99  lits eq                                 4
% 3.55/0.99  fd_pure                                 0
% 3.55/0.99  fd_pseudo                               0
% 3.55/0.99  fd_cond                                 0
% 3.55/0.99  fd_pseudo_cond                          1
% 3.55/0.99  AC symbols                              0
% 3.55/0.99  
% 3.55/0.99  ------ Input Options Time Limit: Unbounded
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  ------ 
% 3.55/0.99  Current options:
% 3.55/0.99  ------ 
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  ------ Proving...
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  % SZS status Theorem for theBenchmark.p
% 3.55/0.99  
% 3.55/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.55/0.99  
% 3.55/0.99  fof(f18,conjecture,(
% 3.55/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f19,negated_conjecture,(
% 3.55/0.99    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 3.55/0.99    inference(negated_conjecture,[],[f18])).
% 3.55/0.99  
% 3.55/0.99  fof(f42,plain,(
% 3.55/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.55/0.99    inference(ennf_transformation,[],[f19])).
% 3.55/0.99  
% 3.55/0.99  fof(f43,plain,(
% 3.55/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.55/0.99    inference(flattening,[],[f42])).
% 3.55/0.99  
% 3.55/0.99  fof(f56,plain,(
% 3.55/0.99    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.55/0.99    introduced(choice_axiom,[])).
% 3.55/0.99  
% 3.55/0.99  fof(f55,plain,(
% 3.55/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v1_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.55/0.99    introduced(choice_axiom,[])).
% 3.55/0.99  
% 3.55/0.99  fof(f57,plain,(
% 3.55/0.99    (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v1_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.55/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f43,f56,f55])).
% 3.55/0.99  
% 3.55/0.99  fof(f89,plain,(
% 3.55/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.55/0.99    inference(cnf_transformation,[],[f57])).
% 3.55/0.99  
% 3.55/0.99  fof(f10,axiom,(
% 3.55/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f28,plain,(
% 3.55/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.55/0.99    inference(ennf_transformation,[],[f10])).
% 3.55/0.99  
% 3.55/0.99  fof(f72,plain,(
% 3.55/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f28])).
% 3.55/0.99  
% 3.55/0.99  fof(f88,plain,(
% 3.55/0.99    l1_pre_topc(sK2)),
% 3.55/0.99    inference(cnf_transformation,[],[f57])).
% 3.55/0.99  
% 3.55/0.99  fof(f6,axiom,(
% 3.55/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f25,plain,(
% 3.55/0.99    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.55/0.99    inference(ennf_transformation,[],[f6])).
% 3.55/0.99  
% 3.55/0.99  fof(f67,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.55/0.99    inference(cnf_transformation,[],[f25])).
% 3.55/0.99  
% 3.55/0.99  fof(f8,axiom,(
% 3.55/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f50,plain,(
% 3.55/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.55/0.99    inference(nnf_transformation,[],[f8])).
% 3.55/0.99  
% 3.55/0.99  fof(f70,plain,(
% 3.55/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f50])).
% 3.55/0.99  
% 3.55/0.99  fof(f5,axiom,(
% 3.55/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f24,plain,(
% 3.55/0.99    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.55/0.99    inference(ennf_transformation,[],[f5])).
% 3.55/0.99  
% 3.55/0.99  fof(f66,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.55/0.99    inference(cnf_transformation,[],[f24])).
% 3.55/0.99  
% 3.55/0.99  fof(f69,plain,(
% 3.55/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.55/0.99    inference(cnf_transformation,[],[f50])).
% 3.55/0.99  
% 3.55/0.99  fof(f14,axiom,(
% 3.55/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f20,plain,(
% 3.55/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 3.55/0.99    inference(pure_predicate_removal,[],[f14])).
% 3.55/0.99  
% 3.55/0.99  fof(f34,plain,(
% 3.55/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.55/0.99    inference(ennf_transformation,[],[f20])).
% 3.55/0.99  
% 3.55/0.99  fof(f35,plain,(
% 3.55/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/0.99    inference(flattening,[],[f34])).
% 3.55/0.99  
% 3.55/0.99  fof(f51,plain,(
% 3.55/0.99    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & ~v2_struct_0(sK1(X0,X1))))),
% 3.55/0.99    introduced(choice_axiom,[])).
% 3.55/0.99  
% 3.55/0.99  fof(f52,plain,(
% 3.55/0.99    ! [X0] : (! [X1] : ((u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & ~v2_struct_0(sK1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f51])).
% 3.55/0.99  
% 3.55/0.99  fof(f77,plain,(
% 3.55/0.99    ( ! [X0,X1] : (m1_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f52])).
% 3.55/0.99  
% 3.55/0.99  fof(f85,plain,(
% 3.55/0.99    ~v2_struct_0(sK2)),
% 3.55/0.99    inference(cnf_transformation,[],[f57])).
% 3.55/0.99  
% 3.55/0.99  fof(f11,axiom,(
% 3.55/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f29,plain,(
% 3.55/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.55/0.99    inference(ennf_transformation,[],[f11])).
% 3.55/0.99  
% 3.55/0.99  fof(f73,plain,(
% 3.55/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f29])).
% 3.55/0.99  
% 3.55/0.99  fof(f90,plain,(
% 3.55/0.99    ~v2_tex_2(sK3,sK2)),
% 3.55/0.99    inference(cnf_transformation,[],[f57])).
% 3.55/0.99  
% 3.55/0.99  fof(f2,axiom,(
% 3.55/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f48,plain,(
% 3.55/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.55/0.99    inference(nnf_transformation,[],[f2])).
% 3.55/0.99  
% 3.55/0.99  fof(f49,plain,(
% 3.55/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.55/0.99    inference(flattening,[],[f48])).
% 3.55/0.99  
% 3.55/0.99  fof(f61,plain,(
% 3.55/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.55/0.99    inference(cnf_transformation,[],[f49])).
% 3.55/0.99  
% 3.55/0.99  fof(f92,plain,(
% 3.55/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.55/0.99    inference(equality_resolution,[],[f61])).
% 3.55/0.99  
% 3.55/0.99  fof(f63,plain,(
% 3.55/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f49])).
% 3.55/0.99  
% 3.55/0.99  fof(f78,plain,(
% 3.55/0.99    ( ! [X0,X1] : (u1_struct_0(sK1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f52])).
% 3.55/0.99  
% 3.55/0.99  fof(f15,axiom,(
% 3.55/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f36,plain,(
% 3.55/0.99    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.55/0.99    inference(ennf_transformation,[],[f15])).
% 3.55/0.99  
% 3.55/0.99  fof(f37,plain,(
% 3.55/0.99    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/0.99    inference(flattening,[],[f36])).
% 3.55/0.99  
% 3.55/0.99  fof(f53,plain,(
% 3.55/0.99    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/0.99    inference(nnf_transformation,[],[f37])).
% 3.55/0.99  
% 3.55/0.99  fof(f80,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f53])).
% 3.55/0.99  
% 3.55/0.99  fof(f93,plain,(
% 3.55/0.99    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/0.99    inference(equality_resolution,[],[f80])).
% 3.55/0.99  
% 3.55/0.99  fof(f13,axiom,(
% 3.55/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f21,plain,(
% 3.55/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 3.55/0.99    inference(pure_predicate_removal,[],[f13])).
% 3.55/0.99  
% 3.55/0.99  fof(f22,plain,(
% 3.55/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v1_tdlat_3(X1)))),
% 3.55/0.99    inference(pure_predicate_removal,[],[f21])).
% 3.55/0.99  
% 3.55/0.99  fof(f32,plain,(
% 3.55/0.99    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.55/0.99    inference(ennf_transformation,[],[f22])).
% 3.55/0.99  
% 3.55/0.99  fof(f33,plain,(
% 3.55/0.99    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/0.99    inference(flattening,[],[f32])).
% 3.55/0.99  
% 3.55/0.99  fof(f75,plain,(
% 3.55/0.99    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f33])).
% 3.55/0.99  
% 3.55/0.99  fof(f86,plain,(
% 3.55/0.99    v2_pre_topc(sK2)),
% 3.55/0.99    inference(cnf_transformation,[],[f57])).
% 3.55/0.99  
% 3.55/0.99  fof(f87,plain,(
% 3.55/0.99    v1_tdlat_3(sK2)),
% 3.55/0.99    inference(cnf_transformation,[],[f57])).
% 3.55/0.99  
% 3.55/0.99  fof(f76,plain,(
% 3.55/0.99    ( ! [X0,X1] : (~v2_struct_0(sK1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f52])).
% 3.55/0.99  
% 3.55/0.99  fof(f1,axiom,(
% 3.55/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f23,plain,(
% 3.55/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.55/0.99    inference(ennf_transformation,[],[f1])).
% 3.55/0.99  
% 3.55/0.99  fof(f44,plain,(
% 3.55/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.55/0.99    inference(nnf_transformation,[],[f23])).
% 3.55/0.99  
% 3.55/0.99  fof(f45,plain,(
% 3.55/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.55/0.99    inference(rectify,[],[f44])).
% 3.55/0.99  
% 3.55/0.99  fof(f46,plain,(
% 3.55/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.55/0.99    introduced(choice_axiom,[])).
% 3.55/0.99  
% 3.55/0.99  fof(f47,plain,(
% 3.55/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.55/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).
% 3.55/0.99  
% 3.55/0.99  fof(f59,plain,(
% 3.55/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f47])).
% 3.55/0.99  
% 3.55/0.99  fof(f9,axiom,(
% 3.55/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f27,plain,(
% 3.55/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.55/0.99    inference(ennf_transformation,[],[f9])).
% 3.55/0.99  
% 3.55/0.99  fof(f71,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f27])).
% 3.55/0.99  
% 3.55/0.99  fof(f4,axiom,(
% 3.55/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f65,plain,(
% 3.55/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.55/0.99    inference(cnf_transformation,[],[f4])).
% 3.55/0.99  
% 3.55/0.99  fof(f3,axiom,(
% 3.55/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f64,plain,(
% 3.55/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.55/0.99    inference(cnf_transformation,[],[f3])).
% 3.55/0.99  
% 3.55/0.99  fof(f17,axiom,(
% 3.55/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f40,plain,(
% 3.55/0.99    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v2_tex_2(X2,X0) & ~v2_tex_2(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.55/0.99    inference(ennf_transformation,[],[f17])).
% 3.55/0.99  
% 3.55/0.99  fof(f41,plain,(
% 3.55/0.99    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v2_tex_2(X2,X0) & ~v2_tex_2(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.55/0.99    inference(flattening,[],[f40])).
% 3.55/0.99  
% 3.55/0.99  fof(f83,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f41])).
% 3.55/0.99  
% 3.55/0.99  fof(f16,axiom,(
% 3.55/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X0) = X1 => (v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)))))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f38,plain,(
% 3.55/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.55/0.99    inference(ennf_transformation,[],[f16])).
% 3.55/0.99  
% 3.55/0.99  fof(f39,plain,(
% 3.55/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/0.99    inference(flattening,[],[f38])).
% 3.55/0.99  
% 3.55/0.99  fof(f54,plain,(
% 3.55/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_tdlat_3(X0)) & (v1_tdlat_3(X0) | ~v2_tex_2(X1,X0))) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/0.99    inference(nnf_transformation,[],[f39])).
% 3.55/0.99  
% 3.55/0.99  fof(f82,plain,(
% 3.55/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_tdlat_3(X0) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f54])).
% 3.55/0.99  
% 3.55/0.99  fof(f95,plain,(
% 3.55/0.99    ( ! [X0] : (v2_tex_2(u1_struct_0(X0),X0) | ~v1_tdlat_3(X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/0.99    inference(equality_resolution,[],[f82])).
% 3.55/0.99  
% 3.55/0.99  cnf(c_28,negated_conjecture,
% 3.55/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.55/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1735,plain,
% 3.55/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_14,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.55/0.99      | ~ l1_pre_topc(X1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_29,negated_conjecture,
% 3.55/0.99      ( l1_pre_topc(sK2) ),
% 3.55/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_767,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.55/0.99      | sK2 != X1 ),
% 3.55/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_768,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.55/0.99      | r1_tarski(k1_tops_1(sK2,X0),X0) ),
% 3.55/0.99      inference(unflattening,[status(thm)],[c_767]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1724,plain,
% 3.55/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.55/0.99      | r1_tarski(k1_tops_1(sK2,X0),X0) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_768]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2023,plain,
% 3.55/0.99      ( r1_tarski(k1_tops_1(sK2,sK3),sK3) = iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_1735,c_1724]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_9,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.55/0.99      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.55/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_11,plain,
% 3.55/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_241,plain,
% 3.55/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.55/0.99      inference(prop_impl,[status(thm)],[c_11]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_242,plain,
% 3.55/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.55/0.99      inference(renaming,[status(thm)],[c_241]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_296,plain,
% 3.55/0.99      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.55/0.99      inference(bin_hyper_res,[status(thm)],[c_9,c_242]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1733,plain,
% 3.55/0.99      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 3.55/0.99      | r1_tarski(X2,X0) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_296]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_4036,plain,
% 3.55/0.99      ( k9_subset_1(sK3,X0,k1_tops_1(sK2,sK3)) = k3_xboole_0(X0,k1_tops_1(sK2,sK3)) ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_2023,c_1733]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_8,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.55/0.99      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.55/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_295,plain,
% 3.55/0.99      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 3.55/0.99      | ~ r1_tarski(X2,X0) ),
% 3.55/0.99      inference(bin_hyper_res,[status(thm)],[c_8,c_242]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1734,plain,
% 3.55/0.99      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 3.55/0.99      | r1_tarski(X2,X0) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_295]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_12,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1737,plain,
% 3.55/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.55/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2721,plain,
% 3.55/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.55/0.99      | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_1734,c_1737]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_4574,plain,
% 3.55/0.99      ( r1_tarski(k1_tops_1(sK2,sK3),sK3) != iProver_top
% 3.55/0.99      | r1_tarski(k3_xboole_0(X0,k1_tops_1(sK2,sK3)),sK3) = iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_4036,c_2721]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_37,plain,
% 3.55/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1926,plain,
% 3.55/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.55/0.99      | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_768]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1927,plain,
% 3.55/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.55/0.99      | r1_tarski(k1_tops_1(sK2,sK3),sK3) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_1926]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_10008,plain,
% 3.55/0.99      ( r1_tarski(k3_xboole_0(X0,k1_tops_1(sK2,sK3)),sK3) = iProver_top ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_4574,c_37,c_1927]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_19,plain,
% 3.55/0.99      ( m1_pre_topc(sK1(X0,X1),X0)
% 3.55/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.55/0.99      | v2_struct_0(X0)
% 3.55/0.99      | ~ l1_pre_topc(X0)
% 3.55/0.99      | v1_xboole_0(X1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_623,plain,
% 3.55/0.99      ( m1_pre_topc(sK1(X0,X1),X0)
% 3.55/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.55/0.99      | v2_struct_0(X0)
% 3.55/0.99      | v1_xboole_0(X1)
% 3.55/0.99      | sK2 != X0 ),
% 3.55/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_624,plain,
% 3.55/0.99      ( m1_pre_topc(sK1(sK2,X0),sK2)
% 3.55/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.55/0.99      | v2_struct_0(sK2)
% 3.55/0.99      | v1_xboole_0(X0) ),
% 3.55/0.99      inference(unflattening,[status(thm)],[c_623]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_32,negated_conjecture,
% 3.55/0.99      ( ~ v2_struct_0(sK2) ),
% 3.55/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_628,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.55/0.99      | m1_pre_topc(sK1(sK2,X0),sK2)
% 3.55/0.99      | v1_xboole_0(X0) ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_624,c_32]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_629,plain,
% 3.55/0.99      ( m1_pre_topc(sK1(sK2,X0),sK2)
% 3.55/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.55/0.99      | v1_xboole_0(X0) ),
% 3.55/0.99      inference(renaming,[status(thm)],[c_628]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1729,plain,
% 3.55/0.99      ( m1_pre_topc(sK1(sK2,X0),sK2) = iProver_top
% 3.55/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.55/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2395,plain,
% 3.55/0.99      ( m1_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
% 3.55/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_1735,c_1729]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_15,plain,
% 3.55/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.55/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.99      | ~ l1_pre_topc(X1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_755,plain,
% 3.55/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.55/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.99      | sK2 != X1 ),
% 3.55/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_756,plain,
% 3.55/0.99      ( ~ m1_pre_topc(X0,sK2)
% 3.55/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.55/0.99      inference(unflattening,[status(thm)],[c_755]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1725,plain,
% 3.55/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.55/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_756]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2347,plain,
% 3.55/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.55/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_1725,c_1737]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_4035,plain,
% 3.55/0.99      ( k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(X1)) = k3_xboole_0(X0,u1_struct_0(X1))
% 3.55/0.99      | m1_pre_topc(X1,sK2) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_2347,c_1733]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_9750,plain,
% 3.55/0.99      ( k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK1(sK2,sK3))) = k3_xboole_0(X0,u1_struct_0(sK1(sK2,sK3)))
% 3.55/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_2395,c_4035]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_27,negated_conjecture,
% 3.55/0.99      ( ~ v2_tex_2(sK3,sK2) ),
% 3.55/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_38,plain,
% 3.55/0.99      ( v2_tex_2(sK3,sK2) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_5,plain,
% 3.55/0.99      ( r1_tarski(X0,X0) ),
% 3.55/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_87,plain,
% 3.55/0.99      ( r1_tarski(sK2,sK2) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_3,plain,
% 3.55/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.55/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_91,plain,
% 3.55/0.99      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_18,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.99      | v2_struct_0(X1)
% 3.55/0.99      | ~ l1_pre_topc(X1)
% 3.55/0.99      | v1_xboole_0(X0)
% 3.55/0.99      | u1_struct_0(sK1(X1,X0)) = X0 ),
% 3.55/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_734,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.99      | v2_struct_0(X1)
% 3.55/0.99      | v1_xboole_0(X0)
% 3.55/0.99      | u1_struct_0(sK1(X1,X0)) = X0
% 3.55/0.99      | sK2 != X1 ),
% 3.55/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_735,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.55/0.99      | v2_struct_0(sK2)
% 3.55/0.99      | v1_xboole_0(X0)
% 3.55/0.99      | u1_struct_0(sK1(sK2,X0)) = X0 ),
% 3.55/0.99      inference(unflattening,[status(thm)],[c_734]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_739,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.55/0.99      | v1_xboole_0(X0)
% 3.55/0.99      | u1_struct_0(sK1(sK2,X0)) = X0 ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_735,c_32]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1929,plain,
% 3.55/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.55/0.99      | v1_xboole_0(sK3)
% 3.55/0.99      | u1_struct_0(sK1(sK2,sK3)) = sK3 ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_739]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1930,plain,
% 3.55/0.99      ( u1_struct_0(sK1(sK2,sK3)) = sK3
% 3.55/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.55/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_1929]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_21,plain,
% 3.55/0.99      ( v2_tex_2(u1_struct_0(X0),X1)
% 3.55/0.99      | ~ m1_pre_topc(X0,X1)
% 3.55/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.99      | v2_struct_0(X1)
% 3.55/0.99      | v2_struct_0(X0)
% 3.55/0.99      | ~ v1_tdlat_3(X0)
% 3.55/0.99      | ~ l1_pre_topc(X1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_176,plain,
% 3.55/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.55/0.99      | v2_tex_2(u1_struct_0(X0),X1)
% 3.55/0.99      | v2_struct_0(X1)
% 3.55/0.99      | v2_struct_0(X0)
% 3.55/0.99      | ~ v1_tdlat_3(X0)
% 3.55/0.99      | ~ l1_pre_topc(X1) ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_21,c_15]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_177,plain,
% 3.55/0.99      ( v2_tex_2(u1_struct_0(X0),X1)
% 3.55/0.99      | ~ m1_pre_topc(X0,X1)
% 3.55/0.99      | v2_struct_0(X0)
% 3.55/0.99      | v2_struct_0(X1)
% 3.55/0.99      | ~ v1_tdlat_3(X0)
% 3.55/0.99      | ~ l1_pre_topc(X1) ),
% 3.55/0.99      inference(renaming,[status(thm)],[c_176]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_651,plain,
% 3.55/0.99      ( v2_tex_2(u1_struct_0(X0),X1)
% 3.55/0.99      | ~ m1_pre_topc(X0,X1)
% 3.55/0.99      | v2_struct_0(X0)
% 3.55/0.99      | v2_struct_0(X1)
% 3.55/0.99      | ~ v1_tdlat_3(X0)
% 3.55/0.99      | sK2 != X1 ),
% 3.55/0.99      inference(resolution_lifted,[status(thm)],[c_177,c_29]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_652,plain,
% 3.55/0.99      ( v2_tex_2(u1_struct_0(X0),sK2)
% 3.55/0.99      | ~ m1_pre_topc(X0,sK2)
% 3.55/0.99      | v2_struct_0(X0)
% 3.55/0.99      | v2_struct_0(sK2)
% 3.55/0.99      | ~ v1_tdlat_3(X0) ),
% 3.55/0.99      inference(unflattening,[status(thm)],[c_651]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_17,plain,
% 3.55/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.55/0.99      | v2_struct_0(X1)
% 3.55/0.99      | ~ v1_tdlat_3(X1)
% 3.55/0.99      | v1_tdlat_3(X0)
% 3.55/0.99      | ~ v2_pre_topc(X1)
% 3.55/0.99      | ~ l1_pre_topc(X1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_31,negated_conjecture,
% 3.55/0.99      ( v2_pre_topc(sK2) ),
% 3.55/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_434,plain,
% 3.55/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.55/0.99      | v2_struct_0(X1)
% 3.55/0.99      | ~ v1_tdlat_3(X1)
% 3.55/0.99      | v1_tdlat_3(X0)
% 3.55/0.99      | ~ l1_pre_topc(X1)
% 3.55/0.99      | sK2 != X1 ),
% 3.55/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_31]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_435,plain,
% 3.55/0.99      ( ~ m1_pre_topc(X0,sK2)
% 3.55/0.99      | v2_struct_0(sK2)
% 3.55/0.99      | v1_tdlat_3(X0)
% 3.55/0.99      | ~ v1_tdlat_3(sK2)
% 3.55/0.99      | ~ l1_pre_topc(sK2) ),
% 3.55/0.99      inference(unflattening,[status(thm)],[c_434]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_30,negated_conjecture,
% 3.55/0.99      ( v1_tdlat_3(sK2) ),
% 3.55/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_437,plain,
% 3.55/0.99      ( ~ m1_pre_topc(X0,sK2) | v1_tdlat_3(X0) ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_435,c_32,c_30,c_29]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_656,plain,
% 3.55/0.99      ( v2_tex_2(u1_struct_0(X0),sK2)
% 3.55/0.99      | ~ m1_pre_topc(X0,sK2)
% 3.55/0.99      | v2_struct_0(X0) ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_652,c_32,c_30,c_29,c_435]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_20,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.99      | v2_struct_0(X1)
% 3.55/0.99      | ~ v2_struct_0(sK1(X1,X0))
% 3.55/0.99      | ~ l1_pre_topc(X1)
% 3.55/0.99      | v1_xboole_0(X0) ),
% 3.55/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_713,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.99      | v2_struct_0(X1)
% 3.55/0.99      | ~ v2_struct_0(sK1(X1,X0))
% 3.55/0.99      | v1_xboole_0(X0)
% 3.55/0.99      | sK2 != X1 ),
% 3.55/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_714,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.55/0.99      | ~ v2_struct_0(sK1(sK2,X0))
% 3.55/0.99      | v2_struct_0(sK2)
% 3.55/0.99      | v1_xboole_0(X0) ),
% 3.55/0.99      inference(unflattening,[status(thm)],[c_713]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_718,plain,
% 3.55/0.99      ( ~ v2_struct_0(sK1(sK2,X0))
% 3.55/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.55/0.99      | v1_xboole_0(X0) ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_714,c_32]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_719,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.55/0.99      | ~ v2_struct_0(sK1(sK2,X0))
% 3.55/0.99      | v1_xboole_0(X0) ),
% 3.55/0.99      inference(renaming,[status(thm)],[c_718]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_824,plain,
% 3.55/0.99      ( v2_tex_2(u1_struct_0(X0),sK2)
% 3.55/0.99      | ~ m1_pre_topc(X0,sK2)
% 3.55/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.55/0.99      | v1_xboole_0(X1)
% 3.55/0.99      | sK1(sK2,X1) != X0 ),
% 3.55/0.99      inference(resolution_lifted,[status(thm)],[c_656,c_719]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_825,plain,
% 3.55/0.99      ( v2_tex_2(u1_struct_0(sK1(sK2,X0)),sK2)
% 3.55/0.99      | ~ m1_pre_topc(sK1(sK2,X0),sK2)
% 3.55/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.55/0.99      | v1_xboole_0(X0) ),
% 3.55/0.99      inference(unflattening,[status(thm)],[c_824]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_829,plain,
% 3.55/0.99      ( v2_tex_2(u1_struct_0(sK1(sK2,X0)),sK2)
% 3.55/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.55/0.99      | v1_xboole_0(X0) ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_825,c_32,c_624]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1954,plain,
% 3.55/0.99      ( v2_tex_2(u1_struct_0(sK1(sK2,sK3)),sK2)
% 3.55/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.55/0.99      | v1_xboole_0(sK3) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_829]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1955,plain,
% 3.55/0.99      ( v2_tex_2(u1_struct_0(sK1(sK2,sK3)),sK2) = iProver_top
% 3.55/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.55/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_1954]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1141,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2672,plain,
% 3.55/0.99      ( X0 != X1
% 3.55/0.99      | X0 = u1_struct_0(sK1(sK2,sK3))
% 3.55/0.99      | u1_struct_0(sK1(sK2,sK3)) != X1 ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_1141]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_3642,plain,
% 3.55/0.99      ( X0 = u1_struct_0(sK1(sK2,sK3))
% 3.55/0.99      | X0 != sK3
% 3.55/0.99      | u1_struct_0(sK1(sK2,sK3)) != sK3 ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_2672]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_4983,plain,
% 3.55/0.99      ( u1_struct_0(sK1(sK2,sK3)) != sK3
% 3.55/0.99      | sK3 = u1_struct_0(sK1(sK2,sK3))
% 3.55/0.99      | sK3 != sK3 ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_3642]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1140,plain,( X0 = X0 ),theory(equality) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_4984,plain,
% 3.55/0.99      ( sK3 = sK3 ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_1140]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1151,plain,
% 3.55/0.99      ( ~ v2_tex_2(X0,X1) | v2_tex_2(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.55/0.99      theory(equality) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2273,plain,
% 3.55/0.99      ( v2_tex_2(X0,X1)
% 3.55/0.99      | ~ v2_tex_2(u1_struct_0(sK1(sK2,sK3)),sK2)
% 3.55/0.99      | X0 != u1_struct_0(sK1(sK2,sK3))
% 3.55/0.99      | X1 != sK2 ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_1151]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_9735,plain,
% 3.55/0.99      ( ~ v2_tex_2(u1_struct_0(sK1(sK2,sK3)),sK2)
% 3.55/0.99      | v2_tex_2(sK3,X0)
% 3.55/0.99      | X0 != sK2
% 3.55/0.99      | sK3 != u1_struct_0(sK1(sK2,sK3)) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_2273]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_9736,plain,
% 3.55/0.99      ( X0 != sK2
% 3.55/0.99      | sK3 != u1_struct_0(sK1(sK2,sK3))
% 3.55/0.99      | v2_tex_2(u1_struct_0(sK1(sK2,sK3)),sK2) != iProver_top
% 3.55/0.99      | v2_tex_2(sK3,X0) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_9735]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_9738,plain,
% 3.55/0.99      ( sK2 != sK2
% 3.55/0.99      | sK3 != u1_struct_0(sK1(sK2,sK3))
% 3.55/0.99      | v2_tex_2(u1_struct_0(sK1(sK2,sK3)),sK2) != iProver_top
% 3.55/0.99      | v2_tex_2(sK3,sK2) = iProver_top ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_9736]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_9804,plain,
% 3.55/0.99      ( v1_xboole_0(sK3) = iProver_top ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_9750,c_37,c_38,c_87,c_91,c_1930,c_1955,c_4983,c_4984,
% 3.55/0.99                 c_9738]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1740,plain,
% 3.55/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1,plain,
% 3.55/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1743,plain,
% 3.55/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.55/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_13,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.55/0.99      | ~ r2_hidden(X2,X0)
% 3.55/0.99      | ~ v1_xboole_0(X1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_300,plain,
% 3.55/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 3.55/0.99      inference(bin_hyper_res,[status(thm)],[c_13,c_242]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1731,plain,
% 3.55/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.55/0.99      | r1_tarski(X1,X2) != iProver_top
% 3.55/0.99      | v1_xboole_0(X2) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_300]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_5827,plain,
% 3.55/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.55/0.99      | r1_tarski(X0,X2) = iProver_top
% 3.55/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_1743,c_1731]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_7155,plain,
% 3.55/0.99      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_1740,c_5827]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1741,plain,
% 3.55/0.99      ( X0 = X1
% 3.55/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.55/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_3147,plain,
% 3.55/0.99      ( k1_tops_1(sK2,sK3) = sK3
% 3.55/0.99      | r1_tarski(sK3,k1_tops_1(sK2,sK3)) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_2023,c_1741]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_7409,plain,
% 3.55/0.99      ( k1_tops_1(sK2,sK3) = sK3 | v1_xboole_0(sK3) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_7155,c_3147]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_9809,plain,
% 3.55/0.99      ( k1_tops_1(sK2,sK3) = sK3 ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_9804,c_7409]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_10014,plain,
% 3.55/0.99      ( r1_tarski(k3_xboole_0(X0,sK3),sK3) = iProver_top ),
% 3.55/0.99      inference(light_normalisation,[status(thm)],[c_10008,c_9809]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_10022,plain,
% 3.55/0.99      ( k3_xboole_0(X0,sK3) = sK3
% 3.55/0.99      | r1_tarski(sK3,k3_xboole_0(X0,sK3)) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_10014,c_1741]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_7404,plain,
% 3.55/0.99      ( X0 = X1
% 3.55/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.55/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_7155,c_1741]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_10019,plain,
% 3.55/0.99      ( k3_xboole_0(X0,sK3) = sK3 | v1_xboole_0(sK3) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_10014,c_7404]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_10704,plain,
% 3.55/0.99      ( k3_xboole_0(X0,sK3) = sK3 ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_10022,c_37,c_38,c_87,c_91,c_1930,c_1955,c_4983,c_4984,
% 3.55/0.99                 c_9738,c_10019]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_7,plain,
% 3.55/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.55/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1739,plain,
% 3.55/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_6,plain,
% 3.55/0.99      ( k2_subset_1(X0) = X0 ),
% 3.55/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1753,plain,
% 3.55/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.55/0.99      inference(light_normalisation,[status(thm)],[c_1739,c_6]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2346,plain,
% 3.55/0.99      ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_1735,c_1737]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_4033,plain,
% 3.55/0.99      ( k9_subset_1(u1_struct_0(sK2),X0,sK3) = k3_xboole_0(X0,sK3) ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_2346,c_1733]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_26,plain,
% 3.55/0.99      ( ~ v2_tex_2(X0,X1)
% 3.55/0.99      | v2_tex_2(k9_subset_1(u1_struct_0(X1),X0,X2),X1)
% 3.55/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.99      | ~ l1_pre_topc(X1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_679,plain,
% 3.55/0.99      ( ~ v2_tex_2(X0,X1)
% 3.55/0.99      | v2_tex_2(k9_subset_1(u1_struct_0(X1),X0,X2),X1)
% 3.55/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/0.99      | sK2 != X1 ),
% 3.55/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_29]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_680,plain,
% 3.55/0.99      ( ~ v2_tex_2(X0,sK2)
% 3.55/0.99      | v2_tex_2(k9_subset_1(u1_struct_0(sK2),X0,X1),sK2)
% 3.55/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.55/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.55/0.99      inference(unflattening,[status(thm)],[c_679]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1728,plain,
% 3.55/0.99      ( v2_tex_2(X0,sK2) != iProver_top
% 3.55/0.99      | v2_tex_2(k9_subset_1(u1_struct_0(sK2),X0,X1),sK2) = iProver_top
% 3.55/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.55/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_680]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_4367,plain,
% 3.55/0.99      ( v2_tex_2(X0,sK2) != iProver_top
% 3.55/0.99      | v2_tex_2(k3_xboole_0(X0,sK3),sK2) = iProver_top
% 3.55/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.55/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_4033,c_1728]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_4591,plain,
% 3.55/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.55/0.99      | v2_tex_2(k3_xboole_0(X0,sK3),sK2) = iProver_top
% 3.55/0.99      | v2_tex_2(X0,sK2) != iProver_top ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_4367,c_37]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_4592,plain,
% 3.55/0.99      ( v2_tex_2(X0,sK2) != iProver_top
% 3.55/0.99      | v2_tex_2(k3_xboole_0(X0,sK3),sK2) = iProver_top
% 3.55/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.55/0.99      inference(renaming,[status(thm)],[c_4591]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_4604,plain,
% 3.55/0.99      ( v2_tex_2(k3_xboole_0(u1_struct_0(sK2),sK3),sK2) = iProver_top
% 3.55/0.99      | v2_tex_2(u1_struct_0(sK2),sK2) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_1753,c_4592]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_23,plain,
% 3.55/0.99      ( v2_tex_2(u1_struct_0(X0),X0)
% 3.55/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.55/0.99      | v2_struct_0(X0)
% 3.55/0.99      | ~ v1_tdlat_3(X0)
% 3.55/0.99      | ~ l1_pre_topc(X0) ),
% 3.55/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_609,plain,
% 3.55/0.99      ( v2_tex_2(u1_struct_0(X0),X0)
% 3.55/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.55/0.99      | v2_struct_0(X0)
% 3.55/0.99      | ~ v1_tdlat_3(X0)
% 3.55/0.99      | sK2 != X0 ),
% 3.55/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_610,plain,
% 3.55/0.99      ( v2_tex_2(u1_struct_0(sK2),sK2)
% 3.55/0.99      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.55/0.99      | v2_struct_0(sK2)
% 3.55/0.99      | ~ v1_tdlat_3(sK2) ),
% 3.55/0.99      inference(unflattening,[status(thm)],[c_609]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_612,plain,
% 3.55/0.99      ( v2_tex_2(u1_struct_0(sK2),sK2)
% 3.55/0.99      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_610,c_32,c_30]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1730,plain,
% 3.55/0.99      ( v2_tex_2(u1_struct_0(sK2),sK2) = iProver_top
% 3.55/0.99      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1790,plain,
% 3.55/0.99      ( v2_tex_2(u1_struct_0(sK2),sK2) = iProver_top ),
% 3.55/0.99      inference(forward_subsumption_resolution,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_1730,c_1753]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_5359,plain,
% 3.55/0.99      ( v2_tex_2(k3_xboole_0(u1_struct_0(sK2),sK3),sK2) = iProver_top ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_4604,c_1790]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_10723,plain,
% 3.55/0.99      ( v2_tex_2(sK3,sK2) = iProver_top ),
% 3.55/0.99      inference(demodulation,[status(thm)],[c_10704,c_5359]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(contradiction,plain,
% 3.55/0.99      ( $false ),
% 3.55/0.99      inference(minisat,[status(thm)],[c_10723,c_38]) ).
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.55/0.99  
% 3.55/0.99  ------                               Statistics
% 3.55/0.99  
% 3.55/0.99  ------ Selected
% 3.55/0.99  
% 3.55/0.99  total_time:                             0.269
% 3.55/0.99  
%------------------------------------------------------------------------------
