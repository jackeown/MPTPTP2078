%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:42 EST 2020

% Result     : Theorem 11.51s
% Output     : CNFRefutation 11.51s
% Verified   : 
% Statistics : Number of formulae       :  199 (1190 expanded)
%              Number of clauses        :  114 ( 405 expanded)
%              Number of leaves         :   22 ( 257 expanded)
%              Depth                    :   24
%              Number of atoms          :  691 (4866 expanded)
%              Number of equality atoms :  235 ( 729 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(sK5,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK4)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_pre_topc(sK4)
      & v1_tdlat_3(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ~ v2_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_pre_topc(sK4)
    & v1_tdlat_3(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f62,f61])).

fof(f97,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f63])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(pure_predicate_removal,[],[f15])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK3(X0,X1)) = X1
        & m1_pre_topc(sK3(X0,X1),X0)
        & ~ v2_struct_0(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK3(X0,X1)) = X1
            & m1_pre_topc(sK3(X0,X1),X0)
            & ~ v2_struct_0(sK3(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f57])).

fof(f86,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK3(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f93,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f96,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f55])).

fof(f80,plain,(
    ! [X0] :
      ( v1_xboole_0(sK2(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f46,plain,(
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

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f95,plain,(
    v1_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f98,plain,(
    ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK3(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK3(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f23,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v1_tdlat_3(X1) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f82,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ( ~ v2_tex_2(X2,X0)
                & ~ v2_tex_2(X1,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ( ~ v2_tex_2(X2,X0)
                & ~ v2_tex_2(X1,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_tdlat_3(X0)
      | u1_struct_0(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f103,plain,(
    ! [X0] :
      ( v2_tex_2(u1_struct_0(X0),X0)
      | ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f90])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1349,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1357,plain,
    ( u1_struct_0(sK3(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3143,plain,
    ( u1_struct_0(sK3(sK4,sK5)) = sK5
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1349,c_1357])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_35,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_38,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6687,plain,
    ( u1_struct_0(sK3(sK4,sK5)) = sK5
    | v1_xboole_0(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3143,c_35,c_38])).

cnf(c_1348,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_15,plain,
    ( ~ l1_pre_topc(X0)
    | v1_xboole_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1362,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1371,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1368,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_215,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_216,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_215])).

cnf(c_277,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_14,c_216])).

cnf(c_1342,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_277])).

cnf(c_5081,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1368,c_1342])).

cnf(c_5352,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1371,c_5081])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1369,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5369,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5352,c_1369])).

cnf(c_5575,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5352,c_5369])).

cnf(c_39063,plain,
    ( sK2(X0) = X1
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1362,c_5575])).

cnf(c_39414,plain,
    ( sK2(sK4) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_39063])).

cnf(c_40018,plain,
    ( u1_struct_0(sK3(sK4,sK5)) = sK5
    | sK2(sK4) = sK5 ),
    inference(superposition,[status(thm)],[c_6687,c_39414])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1360,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_40655,plain,
    ( sK2(sK4) = sK5
    | m1_pre_topc(sK3(sK4,sK5),X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_40018,c_1360])).

cnf(c_32,negated_conjecture,
    ( v1_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_37,plain,
    ( v1_tdlat_3(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_29,negated_conjecture,
    ( ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_40,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK3(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1355,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK3(X1,X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2814,plain,
    ( v2_struct_0(sK3(sK4,sK5)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1349,c_1355])).

cnf(c_6132,plain,
    ( v2_struct_0(sK3(sK4,sK5)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2814,c_35,c_38])).

cnf(c_21,plain,
    ( m1_pre_topc(sK3(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1356,plain,
    ( m1_pre_topc(sK3(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3478,plain,
    ( m1_pre_topc(sK3(sK4,sK5),sK4) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1349,c_1356])).

cnf(c_7171,plain,
    ( m1_pre_topc(sK3(sK4,sK5),sK4) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3478,c_35,c_38])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | v1_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1358,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_tdlat_3(X1) != iProver_top
    | v1_tdlat_3(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1359,plain,
    ( v1_tdlat_3(X0) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1518,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_tdlat_3(X1) != iProver_top
    | v1_tdlat_3(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1358,c_1359])).

cnf(c_7177,plain,
    ( v2_struct_0(sK4) = iProver_top
    | v1_tdlat_3(sK3(sK4,sK5)) = iProver_top
    | v1_tdlat_3(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_7171,c_1518])).

cnf(c_1707,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_10442,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(sK5,u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_10443,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(sK5,u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10442])).

cnf(c_3624,plain,
    ( ~ r2_hidden(sK0(X0,u1_struct_0(X1)),X0)
    | ~ r1_tarski(X0,X2)
    | ~ v1_xboole_0(X2) ),
    inference(instantiation,[status(thm)],[c_277])).

cnf(c_6402,plain,
    ( ~ r2_hidden(sK0(X0,u1_struct_0(X1)),X0)
    | ~ r1_tarski(X0,sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3624])).

cnf(c_10659,plain,
    ( ~ r2_hidden(sK0(sK5,u1_struct_0(X0)),sK5)
    | ~ r1_tarski(sK5,sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_6402])).

cnf(c_10661,plain,
    ( r2_hidden(sK0(sK5,u1_struct_0(X0)),sK5) != iProver_top
    | r1_tarski(sK5,sK5) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10659])).

cnf(c_10660,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_10665,plain,
    ( r1_tarski(sK5,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10660])).

cnf(c_1881,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(X1)),X0)
    | r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_24314,plain,
    ( r2_hidden(sK0(sK5,u1_struct_0(X0)),sK5)
    | r1_tarski(sK5,u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_1881])).

cnf(c_24315,plain,
    ( r2_hidden(sK0(sK5,u1_struct_0(X0)),sK5) = iProver_top
    | r1_tarski(sK5,u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24314])).

cnf(c_23,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_350,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_tex_2(u1_struct_0(X0),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_17])).

cnf(c_351,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_350])).

cnf(c_1340,plain,
    ( v2_tex_2(u1_struct_0(X0),X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_40658,plain,
    ( sK2(sK4) = sK5
    | v2_tex_2(sK5,X0) = iProver_top
    | m1_pre_topc(sK3(sK4,sK5),X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3(sK4,sK5)) = iProver_top
    | v1_tdlat_3(sK3(sK4,sK5)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_40018,c_1340])).

cnf(c_41419,plain,
    ( sK2(sK4) = sK5
    | v2_tex_2(sK5,sK4) = iProver_top
    | m1_pre_topc(sK3(sK4,sK5),sK4) != iProver_top
    | v2_struct_0(sK3(sK4,sK5)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_tdlat_3(sK3(sK4,sK5)) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_40658])).

cnf(c_41961,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | sK2(sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_40655,c_35,c_37,c_38,c_40,c_6132,c_7171,c_7177,c_10443,c_10661,c_10665,c_24315,c_41419])).

cnf(c_41962,plain,
    ( sK2(sK4) = sK5
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_41961])).

cnf(c_41970,plain,
    ( u1_struct_0(sK3(X0,sK5)) = sK5
    | sK2(sK4) = sK5
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_41962,c_1357])).

cnf(c_42931,plain,
    ( sK2(sK4) = sK5
    | v1_xboole_0(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_41970,c_35,c_37,c_38,c_40,c_6132,c_7171,c_7177,c_41419])).

cnf(c_42937,plain,
    ( sK2(sK4) = sK5 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_42931,c_39414])).

cnf(c_8,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1366,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1391,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1366,c_7])).

cnf(c_1364,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_274,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_216])).

cnf(c_1343,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_274])).

cnf(c_5372,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5352,c_1343])).

cnf(c_26700,plain,
    ( k9_subset_1(X0,X1,sK2(X2)) = k3_xboole_0(X1,sK2(X2))
    | l1_pre_topc(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1362,c_5372])).

cnf(c_26767,plain,
    ( k9_subset_1(X0,X1,sK2(sK4)) = k3_xboole_0(X1,sK2(sK4)) ),
    inference(superposition,[status(thm)],[c_1348,c_26700])).

cnf(c_4572,plain,
    ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1368,c_1343])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_273,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_216])).

cnf(c_1344,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_4732,plain,
    ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4572,c_1344])).

cnf(c_14173,plain,
    ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4732,c_1368])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1363,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14177,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_14173,c_1363])).

cnf(c_14430,plain,
    ( k3_xboole_0(X0,X1) = X1
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_14177,c_5369])).

cnf(c_18836,plain,
    ( k3_xboole_0(X0,sK2(X1)) = sK2(X1)
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1362,c_14430])).

cnf(c_19107,plain,
    ( k3_xboole_0(X0,sK2(sK4)) = sK2(sK4) ),
    inference(superposition,[status(thm)],[c_1348,c_18836])).

cnf(c_26768,plain,
    ( k9_subset_1(X0,X1,sK2(sK4)) = sK2(sK4) ),
    inference(demodulation,[status(thm)],[c_26767,c_19107])).

cnf(c_28,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(k9_subset_1(u1_struct_0(X1),X0,X2),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1351,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v2_tex_2(k9_subset_1(u1_struct_0(X1),X0,X2),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_28322,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v2_tex_2(sK2(sK4),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_26768,c_1351])).

cnf(c_28774,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v2_tex_2(sK2(sK4),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(sK2(sK4),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1364,c_28322])).

cnf(c_28801,plain,
    ( v2_tex_2(u1_struct_0(X0),X0) != iProver_top
    | v2_tex_2(sK2(sK4),X0) = iProver_top
    | r1_tarski(sK2(sK4),u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1391,c_28774])).

cnf(c_42944,plain,
    ( v2_tex_2(u1_struct_0(X0),X0) != iProver_top
    | v2_tex_2(sK5,X0) = iProver_top
    | r1_tarski(sK5,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_42937,c_28801])).

cnf(c_43047,plain,
    ( v2_tex_2(u1_struct_0(sK4),sK4) != iProver_top
    | v2_tex_2(sK5,sK4) = iProver_top
    | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_42944])).

cnf(c_1778,plain,
    ( r1_tarski(sK5,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_13,c_30])).

cnf(c_1779,plain,
    ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1778])).

cnf(c_25,plain,
    ( v2_tex_2(u1_struct_0(X0),X0)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1354,plain,
    ( v2_tex_2(u1_struct_0(X0),X0) = iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1507,plain,
    ( v2_tex_2(u1_struct_0(X0),X0) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1354,c_1391])).

cnf(c_1584,plain,
    ( v2_tex_2(u1_struct_0(sK4),sK4) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_tdlat_3(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_43047,c_1779,c_1584,c_40,c_38,c_37,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:29:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.51/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.51/1.98  
% 11.51/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.51/1.98  
% 11.51/1.98  ------  iProver source info
% 11.51/1.98  
% 11.51/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.51/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.51/1.98  git: non_committed_changes: false
% 11.51/1.98  git: last_make_outside_of_git: false
% 11.51/1.98  
% 11.51/1.98  ------ 
% 11.51/1.98  
% 11.51/1.98  ------ Input Options
% 11.51/1.98  
% 11.51/1.98  --out_options                           all
% 11.51/1.98  --tptp_safe_out                         true
% 11.51/1.98  --problem_path                          ""
% 11.51/1.98  --include_path                          ""
% 11.51/1.98  --clausifier                            res/vclausify_rel
% 11.51/1.98  --clausifier_options                    --mode clausify
% 11.51/1.98  --stdin                                 false
% 11.51/1.98  --stats_out                             sel
% 11.51/1.98  
% 11.51/1.98  ------ General Options
% 11.51/1.98  
% 11.51/1.98  --fof                                   false
% 11.51/1.98  --time_out_real                         604.99
% 11.51/1.98  --time_out_virtual                      -1.
% 11.51/1.98  --symbol_type_check                     false
% 11.51/1.98  --clausify_out                          false
% 11.51/1.98  --sig_cnt_out                           false
% 11.51/1.98  --trig_cnt_out                          false
% 11.51/1.98  --trig_cnt_out_tolerance                1.
% 11.51/1.98  --trig_cnt_out_sk_spl                   false
% 11.51/1.98  --abstr_cl_out                          false
% 11.51/1.98  
% 11.51/1.98  ------ Global Options
% 11.51/1.98  
% 11.51/1.98  --schedule                              none
% 11.51/1.98  --add_important_lit                     false
% 11.51/1.98  --prop_solver_per_cl                    1000
% 11.51/1.98  --min_unsat_core                        false
% 11.51/1.98  --soft_assumptions                      false
% 11.51/1.98  --soft_lemma_size                       3
% 11.51/1.98  --prop_impl_unit_size                   0
% 11.51/1.98  --prop_impl_unit                        []
% 11.51/1.98  --share_sel_clauses                     true
% 11.51/1.98  --reset_solvers                         false
% 11.51/1.98  --bc_imp_inh                            [conj_cone]
% 11.51/1.98  --conj_cone_tolerance                   3.
% 11.51/1.98  --extra_neg_conj                        none
% 11.51/1.98  --large_theory_mode                     true
% 11.51/1.98  --prolific_symb_bound                   200
% 11.51/1.98  --lt_threshold                          2000
% 11.51/1.98  --clause_weak_htbl                      true
% 11.51/1.98  --gc_record_bc_elim                     false
% 11.51/1.98  
% 11.51/1.98  ------ Preprocessing Options
% 11.51/1.98  
% 11.51/1.98  --preprocessing_flag                    true
% 11.51/1.98  --time_out_prep_mult                    0.1
% 11.51/1.98  --splitting_mode                        input
% 11.51/1.98  --splitting_grd                         true
% 11.51/1.98  --splitting_cvd                         false
% 11.51/1.98  --splitting_cvd_svl                     false
% 11.51/1.98  --splitting_nvd                         32
% 11.51/1.98  --sub_typing                            true
% 11.51/1.98  --prep_gs_sim                           false
% 11.51/1.98  --prep_unflatten                        true
% 11.51/1.98  --prep_res_sim                          true
% 11.51/1.98  --prep_upred                            true
% 11.51/1.98  --prep_sem_filter                       exhaustive
% 11.51/1.98  --prep_sem_filter_out                   false
% 11.51/1.98  --pred_elim                             false
% 11.51/1.98  --res_sim_input                         true
% 11.51/1.98  --eq_ax_congr_red                       true
% 11.51/1.98  --pure_diseq_elim                       true
% 11.51/1.98  --brand_transform                       false
% 11.51/1.98  --non_eq_to_eq                          false
% 11.51/1.98  --prep_def_merge                        true
% 11.51/1.98  --prep_def_merge_prop_impl              false
% 11.51/1.98  --prep_def_merge_mbd                    true
% 11.51/1.98  --prep_def_merge_tr_red                 false
% 11.51/1.98  --prep_def_merge_tr_cl                  false
% 11.51/1.98  --smt_preprocessing                     true
% 11.51/1.98  --smt_ac_axioms                         fast
% 11.51/1.98  --preprocessed_out                      false
% 11.51/1.98  --preprocessed_stats                    false
% 11.51/1.98  
% 11.51/1.98  ------ Abstraction refinement Options
% 11.51/1.98  
% 11.51/1.98  --abstr_ref                             []
% 11.51/1.98  --abstr_ref_prep                        false
% 11.51/1.98  --abstr_ref_until_sat                   false
% 11.51/1.98  --abstr_ref_sig_restrict                funpre
% 11.51/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.51/1.98  --abstr_ref_under                       []
% 11.51/1.98  
% 11.51/1.98  ------ SAT Options
% 11.51/1.98  
% 11.51/1.98  --sat_mode                              false
% 11.51/1.98  --sat_fm_restart_options                ""
% 11.51/1.98  --sat_gr_def                            false
% 11.51/1.98  --sat_epr_types                         true
% 11.51/1.98  --sat_non_cyclic_types                  false
% 11.51/1.98  --sat_finite_models                     false
% 11.51/1.98  --sat_fm_lemmas                         false
% 11.51/1.98  --sat_fm_prep                           false
% 11.51/1.98  --sat_fm_uc_incr                        true
% 11.51/1.98  --sat_out_model                         small
% 11.51/1.98  --sat_out_clauses                       false
% 11.51/1.98  
% 11.51/1.98  ------ QBF Options
% 11.51/1.98  
% 11.51/1.98  --qbf_mode                              false
% 11.51/1.98  --qbf_elim_univ                         false
% 11.51/1.98  --qbf_dom_inst                          none
% 11.51/1.98  --qbf_dom_pre_inst                      false
% 11.51/1.98  --qbf_sk_in                             false
% 11.51/1.98  --qbf_pred_elim                         true
% 11.51/1.98  --qbf_split                             512
% 11.51/1.98  
% 11.51/1.98  ------ BMC1 Options
% 11.51/1.98  
% 11.51/1.98  --bmc1_incremental                      false
% 11.51/1.98  --bmc1_axioms                           reachable_all
% 11.51/1.98  --bmc1_min_bound                        0
% 11.51/1.98  --bmc1_max_bound                        -1
% 11.51/1.98  --bmc1_max_bound_default                -1
% 11.51/1.98  --bmc1_symbol_reachability              true
% 11.51/1.98  --bmc1_property_lemmas                  false
% 11.51/1.98  --bmc1_k_induction                      false
% 11.51/1.98  --bmc1_non_equiv_states                 false
% 11.51/1.98  --bmc1_deadlock                         false
% 11.51/1.98  --bmc1_ucm                              false
% 11.51/1.98  --bmc1_add_unsat_core                   none
% 11.51/1.98  --bmc1_unsat_core_children              false
% 11.51/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.51/1.98  --bmc1_out_stat                         full
% 11.51/1.98  --bmc1_ground_init                      false
% 11.51/1.98  --bmc1_pre_inst_next_state              false
% 11.51/1.98  --bmc1_pre_inst_state                   false
% 11.51/1.98  --bmc1_pre_inst_reach_state             false
% 11.51/1.98  --bmc1_out_unsat_core                   false
% 11.51/1.98  --bmc1_aig_witness_out                  false
% 11.51/1.98  --bmc1_verbose                          false
% 11.51/1.98  --bmc1_dump_clauses_tptp                false
% 11.51/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.51/1.98  --bmc1_dump_file                        -
% 11.51/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.51/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.51/1.98  --bmc1_ucm_extend_mode                  1
% 11.51/1.98  --bmc1_ucm_init_mode                    2
% 11.51/1.98  --bmc1_ucm_cone_mode                    none
% 11.51/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.51/1.98  --bmc1_ucm_relax_model                  4
% 11.51/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.51/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.51/1.98  --bmc1_ucm_layered_model                none
% 11.51/1.98  --bmc1_ucm_max_lemma_size               10
% 11.51/1.98  
% 11.51/1.98  ------ AIG Options
% 11.51/1.98  
% 11.51/1.98  --aig_mode                              false
% 11.51/1.98  
% 11.51/1.98  ------ Instantiation Options
% 11.51/1.98  
% 11.51/1.98  --instantiation_flag                    true
% 11.51/1.98  --inst_sos_flag                         false
% 11.51/1.98  --inst_sos_phase                        true
% 11.51/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.51/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.51/1.98  --inst_lit_sel_side                     num_symb
% 11.51/1.98  --inst_solver_per_active                1400
% 11.51/1.98  --inst_solver_calls_frac                1.
% 11.51/1.98  --inst_passive_queue_type               priority_queues
% 11.51/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.51/1.98  --inst_passive_queues_freq              [25;2]
% 11.51/1.98  --inst_dismatching                      true
% 11.51/1.98  --inst_eager_unprocessed_to_passive     true
% 11.51/1.98  --inst_prop_sim_given                   true
% 11.51/1.98  --inst_prop_sim_new                     false
% 11.51/1.98  --inst_subs_new                         false
% 11.51/1.98  --inst_eq_res_simp                      false
% 11.51/1.98  --inst_subs_given                       false
% 11.51/1.98  --inst_orphan_elimination               true
% 11.51/1.98  --inst_learning_loop_flag               true
% 11.51/1.98  --inst_learning_start                   3000
% 11.51/1.98  --inst_learning_factor                  2
% 11.51/1.98  --inst_start_prop_sim_after_learn       3
% 11.51/1.98  --inst_sel_renew                        solver
% 11.51/1.98  --inst_lit_activity_flag                true
% 11.51/1.98  --inst_restr_to_given                   false
% 11.51/1.98  --inst_activity_threshold               500
% 11.51/1.98  --inst_out_proof                        true
% 11.51/1.98  
% 11.51/1.98  ------ Resolution Options
% 11.51/1.98  
% 11.51/1.98  --resolution_flag                       true
% 11.51/1.98  --res_lit_sel                           adaptive
% 11.51/1.98  --res_lit_sel_side                      none
% 11.51/1.98  --res_ordering                          kbo
% 11.51/1.98  --res_to_prop_solver                    active
% 11.51/1.98  --res_prop_simpl_new                    false
% 11.51/1.98  --res_prop_simpl_given                  true
% 11.51/1.98  --res_passive_queue_type                priority_queues
% 11.51/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.51/1.98  --res_passive_queues_freq               [15;5]
% 11.51/1.98  --res_forward_subs                      full
% 11.51/1.98  --res_backward_subs                     full
% 11.51/1.98  --res_forward_subs_resolution           true
% 11.51/1.98  --res_backward_subs_resolution          true
% 11.51/1.98  --res_orphan_elimination                true
% 11.51/1.98  --res_time_limit                        2.
% 11.51/1.98  --res_out_proof                         true
% 11.51/1.98  
% 11.51/1.98  ------ Superposition Options
% 11.51/1.98  
% 11.51/1.98  --superposition_flag                    true
% 11.51/1.98  --sup_passive_queue_type                priority_queues
% 11.51/1.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.51/1.98  --sup_passive_queues_freq               [1;4]
% 11.51/1.98  --demod_completeness_check              fast
% 11.51/1.98  --demod_use_ground                      true
% 11.51/1.98  --sup_to_prop_solver                    passive
% 11.51/1.98  --sup_prop_simpl_new                    true
% 11.51/1.98  --sup_prop_simpl_given                  true
% 11.51/1.98  --sup_fun_splitting                     false
% 11.51/1.98  --sup_smt_interval                      50000
% 11.51/1.98  
% 11.51/1.98  ------ Superposition Simplification Setup
% 11.51/1.98  
% 11.51/1.98  --sup_indices_passive                   []
% 11.51/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.51/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.51/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.51/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.51/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.51/1.98  --sup_full_bw                           [BwDemod]
% 11.51/1.98  --sup_immed_triv                        [TrivRules]
% 11.51/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.51/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.51/1.98  --sup_immed_bw_main                     []
% 11.51/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.51/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.51/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.51/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.51/1.98  
% 11.51/1.98  ------ Combination Options
% 11.51/1.98  
% 11.51/1.98  --comb_res_mult                         3
% 11.51/1.98  --comb_sup_mult                         2
% 11.51/1.98  --comb_inst_mult                        10
% 11.51/1.98  
% 11.51/1.98  ------ Debug Options
% 11.51/1.98  
% 11.51/1.98  --dbg_backtrace                         false
% 11.51/1.98  --dbg_dump_prop_clauses                 false
% 11.51/1.98  --dbg_dump_prop_clauses_file            -
% 11.51/1.98  --dbg_out_stat                          false
% 11.51/1.98  ------ Parsing...
% 11.51/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.51/1.98  
% 11.51/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.51/1.98  
% 11.51/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.51/1.98  
% 11.51/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.51/1.98  ------ Proving...
% 11.51/1.98  ------ Problem Properties 
% 11.51/1.98  
% 11.51/1.98  
% 11.51/1.98  clauses                                 34
% 11.51/1.98  conjectures                             6
% 11.51/1.98  EPR                                     12
% 11.51/1.98  Horn                                    25
% 11.51/1.98  unary                                   10
% 11.51/1.98  binary                                  8
% 11.51/1.98  lits                                    97
% 11.51/1.98  lits eq                                 4
% 11.51/1.98  fd_pure                                 0
% 11.51/1.98  fd_pseudo                               0
% 11.51/1.98  fd_cond                                 0
% 11.51/1.98  fd_pseudo_cond                          1
% 11.51/1.98  AC symbols                              0
% 11.51/1.98  
% 11.51/1.98  ------ Input Options Time Limit: Unbounded
% 11.51/1.98  
% 11.51/1.98  
% 11.51/1.98  ------ 
% 11.51/1.98  Current options:
% 11.51/1.98  ------ 
% 11.51/1.98  
% 11.51/1.98  ------ Input Options
% 11.51/1.98  
% 11.51/1.98  --out_options                           all
% 11.51/1.98  --tptp_safe_out                         true
% 11.51/1.98  --problem_path                          ""
% 11.51/1.98  --include_path                          ""
% 11.51/1.98  --clausifier                            res/vclausify_rel
% 11.51/1.98  --clausifier_options                    --mode clausify
% 11.51/1.98  --stdin                                 false
% 11.51/1.98  --stats_out                             sel
% 11.51/1.98  
% 11.51/1.98  ------ General Options
% 11.51/1.98  
% 11.51/1.98  --fof                                   false
% 11.51/1.98  --time_out_real                         604.99
% 11.51/1.98  --time_out_virtual                      -1.
% 11.51/1.98  --symbol_type_check                     false
% 11.51/1.98  --clausify_out                          false
% 11.51/1.98  --sig_cnt_out                           false
% 11.51/1.98  --trig_cnt_out                          false
% 11.51/1.98  --trig_cnt_out_tolerance                1.
% 11.51/1.98  --trig_cnt_out_sk_spl                   false
% 11.51/1.98  --abstr_cl_out                          false
% 11.51/1.98  
% 11.51/1.98  ------ Global Options
% 11.51/1.98  
% 11.51/1.98  --schedule                              none
% 11.51/1.98  --add_important_lit                     false
% 11.51/1.98  --prop_solver_per_cl                    1000
% 11.51/1.98  --min_unsat_core                        false
% 11.51/1.98  --soft_assumptions                      false
% 11.51/1.98  --soft_lemma_size                       3
% 11.51/1.98  --prop_impl_unit_size                   0
% 11.51/1.98  --prop_impl_unit                        []
% 11.51/1.98  --share_sel_clauses                     true
% 11.51/1.98  --reset_solvers                         false
% 11.51/1.98  --bc_imp_inh                            [conj_cone]
% 11.51/1.98  --conj_cone_tolerance                   3.
% 11.51/1.98  --extra_neg_conj                        none
% 11.51/1.98  --large_theory_mode                     true
% 11.51/1.98  --prolific_symb_bound                   200
% 11.51/1.98  --lt_threshold                          2000
% 11.51/1.98  --clause_weak_htbl                      true
% 11.51/1.98  --gc_record_bc_elim                     false
% 11.51/1.98  
% 11.51/1.98  ------ Preprocessing Options
% 11.51/1.98  
% 11.51/1.98  --preprocessing_flag                    true
% 11.51/1.98  --time_out_prep_mult                    0.1
% 11.51/1.98  --splitting_mode                        input
% 11.51/1.98  --splitting_grd                         true
% 11.51/1.98  --splitting_cvd                         false
% 11.51/1.98  --splitting_cvd_svl                     false
% 11.51/1.98  --splitting_nvd                         32
% 11.51/1.98  --sub_typing                            true
% 11.51/1.98  --prep_gs_sim                           false
% 11.51/1.98  --prep_unflatten                        true
% 11.51/1.98  --prep_res_sim                          true
% 11.51/1.98  --prep_upred                            true
% 11.51/1.98  --prep_sem_filter                       exhaustive
% 11.51/1.98  --prep_sem_filter_out                   false
% 11.51/1.98  --pred_elim                             false
% 11.51/1.98  --res_sim_input                         true
% 11.51/1.98  --eq_ax_congr_red                       true
% 11.51/1.98  --pure_diseq_elim                       true
% 11.51/1.98  --brand_transform                       false
% 11.51/1.98  --non_eq_to_eq                          false
% 11.51/1.98  --prep_def_merge                        true
% 11.51/1.98  --prep_def_merge_prop_impl              false
% 11.51/1.98  --prep_def_merge_mbd                    true
% 11.51/1.98  --prep_def_merge_tr_red                 false
% 11.51/1.98  --prep_def_merge_tr_cl                  false
% 11.51/1.98  --smt_preprocessing                     true
% 11.51/1.98  --smt_ac_axioms                         fast
% 11.51/1.98  --preprocessed_out                      false
% 11.51/1.98  --preprocessed_stats                    false
% 11.51/1.98  
% 11.51/1.98  ------ Abstraction refinement Options
% 11.51/1.98  
% 11.51/1.98  --abstr_ref                             []
% 11.51/1.98  --abstr_ref_prep                        false
% 11.51/1.98  --abstr_ref_until_sat                   false
% 11.51/1.98  --abstr_ref_sig_restrict                funpre
% 11.51/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.51/1.98  --abstr_ref_under                       []
% 11.51/1.98  
% 11.51/1.98  ------ SAT Options
% 11.51/1.98  
% 11.51/1.98  --sat_mode                              false
% 11.51/1.98  --sat_fm_restart_options                ""
% 11.51/1.98  --sat_gr_def                            false
% 11.51/1.98  --sat_epr_types                         true
% 11.51/1.98  --sat_non_cyclic_types                  false
% 11.51/1.98  --sat_finite_models                     false
% 11.51/1.98  --sat_fm_lemmas                         false
% 11.51/1.98  --sat_fm_prep                           false
% 11.51/1.98  --sat_fm_uc_incr                        true
% 11.51/1.98  --sat_out_model                         small
% 11.51/1.98  --sat_out_clauses                       false
% 11.51/1.98  
% 11.51/1.98  ------ QBF Options
% 11.51/1.98  
% 11.51/1.98  --qbf_mode                              false
% 11.51/1.98  --qbf_elim_univ                         false
% 11.51/1.98  --qbf_dom_inst                          none
% 11.51/1.98  --qbf_dom_pre_inst                      false
% 11.51/1.98  --qbf_sk_in                             false
% 11.51/1.98  --qbf_pred_elim                         true
% 11.51/1.98  --qbf_split                             512
% 11.51/1.98  
% 11.51/1.98  ------ BMC1 Options
% 11.51/1.98  
% 11.51/1.98  --bmc1_incremental                      false
% 11.51/1.98  --bmc1_axioms                           reachable_all
% 11.51/1.98  --bmc1_min_bound                        0
% 11.51/1.98  --bmc1_max_bound                        -1
% 11.51/1.98  --bmc1_max_bound_default                -1
% 11.51/1.98  --bmc1_symbol_reachability              true
% 11.51/1.98  --bmc1_property_lemmas                  false
% 11.51/1.98  --bmc1_k_induction                      false
% 11.51/1.98  --bmc1_non_equiv_states                 false
% 11.51/1.98  --bmc1_deadlock                         false
% 11.51/1.98  --bmc1_ucm                              false
% 11.51/1.98  --bmc1_add_unsat_core                   none
% 11.51/1.98  --bmc1_unsat_core_children              false
% 11.51/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.51/1.98  --bmc1_out_stat                         full
% 11.51/1.98  --bmc1_ground_init                      false
% 11.51/1.98  --bmc1_pre_inst_next_state              false
% 11.51/1.98  --bmc1_pre_inst_state                   false
% 11.51/1.98  --bmc1_pre_inst_reach_state             false
% 11.51/1.98  --bmc1_out_unsat_core                   false
% 11.51/1.98  --bmc1_aig_witness_out                  false
% 11.51/1.98  --bmc1_verbose                          false
% 11.51/1.98  --bmc1_dump_clauses_tptp                false
% 11.51/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.51/1.98  --bmc1_dump_file                        -
% 11.51/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.51/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.51/1.98  --bmc1_ucm_extend_mode                  1
% 11.51/1.98  --bmc1_ucm_init_mode                    2
% 11.51/1.98  --bmc1_ucm_cone_mode                    none
% 11.51/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.51/1.98  --bmc1_ucm_relax_model                  4
% 11.51/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.51/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.51/1.98  --bmc1_ucm_layered_model                none
% 11.51/1.98  --bmc1_ucm_max_lemma_size               10
% 11.51/1.98  
% 11.51/1.98  ------ AIG Options
% 11.51/1.98  
% 11.51/1.98  --aig_mode                              false
% 11.51/1.98  
% 11.51/1.98  ------ Instantiation Options
% 11.51/1.98  
% 11.51/1.98  --instantiation_flag                    true
% 11.51/1.98  --inst_sos_flag                         false
% 11.51/1.98  --inst_sos_phase                        true
% 11.51/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.51/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.51/1.98  --inst_lit_sel_side                     num_symb
% 11.51/1.98  --inst_solver_per_active                1400
% 11.51/1.98  --inst_solver_calls_frac                1.
% 11.51/1.98  --inst_passive_queue_type               priority_queues
% 11.51/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.51/1.98  --inst_passive_queues_freq              [25;2]
% 11.51/1.98  --inst_dismatching                      true
% 11.51/1.98  --inst_eager_unprocessed_to_passive     true
% 11.51/1.98  --inst_prop_sim_given                   true
% 11.51/1.98  --inst_prop_sim_new                     false
% 11.51/1.98  --inst_subs_new                         false
% 11.51/1.98  --inst_eq_res_simp                      false
% 11.51/1.98  --inst_subs_given                       false
% 11.51/1.98  --inst_orphan_elimination               true
% 11.51/1.98  --inst_learning_loop_flag               true
% 11.51/1.98  --inst_learning_start                   3000
% 11.51/1.98  --inst_learning_factor                  2
% 11.51/1.98  --inst_start_prop_sim_after_learn       3
% 11.51/1.98  --inst_sel_renew                        solver
% 11.51/1.98  --inst_lit_activity_flag                true
% 11.51/1.98  --inst_restr_to_given                   false
% 11.51/1.98  --inst_activity_threshold               500
% 11.51/1.98  --inst_out_proof                        true
% 11.51/1.98  
% 11.51/1.98  ------ Resolution Options
% 11.51/1.98  
% 11.51/1.98  --resolution_flag                       true
% 11.51/1.98  --res_lit_sel                           adaptive
% 11.51/1.98  --res_lit_sel_side                      none
% 11.51/1.98  --res_ordering                          kbo
% 11.51/1.98  --res_to_prop_solver                    active
% 11.51/1.98  --res_prop_simpl_new                    false
% 11.51/1.98  --res_prop_simpl_given                  true
% 11.51/1.98  --res_passive_queue_type                priority_queues
% 11.51/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.51/1.98  --res_passive_queues_freq               [15;5]
% 11.51/1.98  --res_forward_subs                      full
% 11.51/1.98  --res_backward_subs                     full
% 11.51/1.98  --res_forward_subs_resolution           true
% 11.51/1.98  --res_backward_subs_resolution          true
% 11.51/1.98  --res_orphan_elimination                true
% 11.51/1.98  --res_time_limit                        2.
% 11.51/1.98  --res_out_proof                         true
% 11.51/1.98  
% 11.51/1.98  ------ Superposition Options
% 11.51/1.98  
% 11.51/1.98  --superposition_flag                    true
% 11.51/1.98  --sup_passive_queue_type                priority_queues
% 11.51/1.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.51/1.98  --sup_passive_queues_freq               [1;4]
% 11.51/1.98  --demod_completeness_check              fast
% 11.51/1.98  --demod_use_ground                      true
% 11.51/1.98  --sup_to_prop_solver                    passive
% 11.51/1.98  --sup_prop_simpl_new                    true
% 11.51/1.98  --sup_prop_simpl_given                  true
% 11.51/1.98  --sup_fun_splitting                     false
% 11.51/1.98  --sup_smt_interval                      50000
% 11.51/1.98  
% 11.51/1.98  ------ Superposition Simplification Setup
% 11.51/1.98  
% 11.51/1.98  --sup_indices_passive                   []
% 11.51/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.51/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.51/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.51/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.51/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.51/1.98  --sup_full_bw                           [BwDemod]
% 11.51/1.98  --sup_immed_triv                        [TrivRules]
% 11.51/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.51/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.51/1.98  --sup_immed_bw_main                     []
% 11.51/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.51/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.51/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.51/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.51/1.98  
% 11.51/1.98  ------ Combination Options
% 11.51/1.98  
% 11.51/1.98  --comb_res_mult                         3
% 11.51/1.98  --comb_sup_mult                         2
% 11.51/1.98  --comb_inst_mult                        10
% 11.51/1.98  
% 11.51/1.98  ------ Debug Options
% 11.51/1.98  
% 11.51/1.98  --dbg_backtrace                         false
% 11.51/1.98  --dbg_dump_prop_clauses                 false
% 11.51/1.98  --dbg_dump_prop_clauses_file            -
% 11.51/1.98  --dbg_out_stat                          false
% 11.51/1.98  
% 11.51/1.98  
% 11.51/1.98  
% 11.51/1.98  
% 11.51/1.98  ------ Proving...
% 11.51/1.98  
% 11.51/1.98  
% 11.51/1.98  % SZS status Theorem for theBenchmark.p
% 11.51/1.98  
% 11.51/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.51/1.98  
% 11.51/1.98  fof(f19,conjecture,(
% 11.51/1.98    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 11.51/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.51/1.98  
% 11.51/1.98  fof(f20,negated_conjecture,(
% 11.51/1.98    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 11.51/1.98    inference(negated_conjecture,[],[f19])).
% 11.51/1.98  
% 11.51/1.98  fof(f44,plain,(
% 11.51/1.98    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.51/1.98    inference(ennf_transformation,[],[f20])).
% 11.51/1.98  
% 11.51/1.98  fof(f45,plain,(
% 11.51/1.98    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.51/1.98    inference(flattening,[],[f44])).
% 11.51/1.98  
% 11.51/1.98  fof(f62,plain,(
% 11.51/1.98    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(sK5,X0) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.51/1.98    introduced(choice_axiom,[])).
% 11.51/1.98  
% 11.51/1.98  fof(f61,plain,(
% 11.51/1.98    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4) & v1_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 11.51/1.98    introduced(choice_axiom,[])).
% 11.51/1.98  
% 11.51/1.98  fof(f63,plain,(
% 11.51/1.98    (~v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4) & v1_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 11.51/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f62,f61])).
% 11.51/1.98  
% 11.51/1.98  fof(f97,plain,(
% 11.51/1.98    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 11.51/1.98    inference(cnf_transformation,[],[f63])).
% 11.51/1.98  
% 11.51/1.98  fof(f15,axiom,(
% 11.51/1.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 11.51/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.51/1.98  
% 11.51/1.98  fof(f21,plain,(
% 11.51/1.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 11.51/1.98    inference(pure_predicate_removal,[],[f15])).
% 11.51/1.98  
% 11.51/1.98  fof(f36,plain,(
% 11.51/1.98    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 11.51/1.98    inference(ennf_transformation,[],[f21])).
% 11.51/1.98  
% 11.51/1.98  fof(f37,plain,(
% 11.51/1.98    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 11.51/1.98    inference(flattening,[],[f36])).
% 11.51/1.98  
% 11.51/1.98  fof(f57,plain,(
% 11.51/1.98    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK3(X0,X1)) = X1 & m1_pre_topc(sK3(X0,X1),X0) & ~v2_struct_0(sK3(X0,X1))))),
% 11.51/1.98    introduced(choice_axiom,[])).
% 11.51/1.98  
% 11.51/1.98  fof(f58,plain,(
% 11.51/1.98    ! [X0] : (! [X1] : ((u1_struct_0(sK3(X0,X1)) = X1 & m1_pre_topc(sK3(X0,X1),X0) & ~v2_struct_0(sK3(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 11.51/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f57])).
% 11.51/1.98  
% 11.51/1.98  fof(f86,plain,(
% 11.51/1.98    ( ! [X0,X1] : (u1_struct_0(sK3(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.51/1.98    inference(cnf_transformation,[],[f58])).
% 11.51/1.98  
% 11.51/1.98  fof(f93,plain,(
% 11.51/1.98    ~v2_struct_0(sK4)),
% 11.51/1.98    inference(cnf_transformation,[],[f63])).
% 11.51/1.98  
% 11.51/1.98  fof(f96,plain,(
% 11.51/1.98    l1_pre_topc(sK4)),
% 11.51/1.98    inference(cnf_transformation,[],[f63])).
% 11.51/1.98  
% 11.51/1.98  fof(f11,axiom,(
% 11.51/1.98    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.51/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.51/1.98  
% 11.51/1.98  fof(f30,plain,(
% 11.51/1.98    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.51/1.98    inference(ennf_transformation,[],[f11])).
% 11.51/1.98  
% 11.51/1.98  fof(f55,plain,(
% 11.51/1.98    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.51/1.98    introduced(choice_axiom,[])).
% 11.51/1.98  
% 11.51/1.98  fof(f56,plain,(
% 11.51/1.98    ! [X0] : ((v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.51/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f55])).
% 11.51/1.98  
% 11.51/1.98  fof(f80,plain,(
% 11.51/1.98    ( ! [X0] : (v1_xboole_0(sK2(X0)) | ~l1_pre_topc(X0)) )),
% 11.51/1.98    inference(cnf_transformation,[],[f56])).
% 11.51/1.98  
% 11.51/1.98  fof(f1,axiom,(
% 11.51/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.51/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.51/1.98  
% 11.51/1.98  fof(f24,plain,(
% 11.51/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.51/1.98    inference(ennf_transformation,[],[f1])).
% 11.51/1.98  
% 11.51/1.98  fof(f46,plain,(
% 11.51/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.51/1.98    inference(nnf_transformation,[],[f24])).
% 11.51/1.98  
% 11.51/1.98  fof(f47,plain,(
% 11.51/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.51/1.98    inference(rectify,[],[f46])).
% 11.51/1.98  
% 11.51/1.98  fof(f48,plain,(
% 11.51/1.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.51/1.98    introduced(choice_axiom,[])).
% 11.51/1.98  
% 11.51/1.98  fof(f49,plain,(
% 11.51/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.51/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 11.51/1.98  
% 11.51/1.98  fof(f65,plain,(
% 11.51/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.51/1.98    inference(cnf_transformation,[],[f49])).
% 11.51/1.98  
% 11.51/1.98  fof(f2,axiom,(
% 11.51/1.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.51/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.51/1.98  
% 11.51/1.98  fof(f50,plain,(
% 11.51/1.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.51/1.98    inference(nnf_transformation,[],[f2])).
% 11.51/1.98  
% 11.51/1.98  fof(f51,plain,(
% 11.51/1.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.51/1.98    inference(flattening,[],[f50])).
% 11.51/1.98  
% 11.51/1.98  fof(f67,plain,(
% 11.51/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.51/1.98    inference(cnf_transformation,[],[f51])).
% 11.51/1.98  
% 11.51/1.98  fof(f100,plain,(
% 11.51/1.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.51/1.98    inference(equality_resolution,[],[f67])).
% 11.51/1.98  
% 11.51/1.98  fof(f10,axiom,(
% 11.51/1.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 11.51/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.51/1.98  
% 11.51/1.98  fof(f29,plain,(
% 11.51/1.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 11.51/1.98    inference(ennf_transformation,[],[f10])).
% 11.51/1.98  
% 11.51/1.98  fof(f78,plain,(
% 11.51/1.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 11.51/1.98    inference(cnf_transformation,[],[f29])).
% 11.51/1.98  
% 11.51/1.98  fof(f9,axiom,(
% 11.51/1.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.51/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.51/1.98  
% 11.51/1.98  fof(f54,plain,(
% 11.51/1.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.51/1.98    inference(nnf_transformation,[],[f9])).
% 11.51/1.98  
% 11.51/1.98  fof(f77,plain,(
% 11.51/1.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.51/1.98    inference(cnf_transformation,[],[f54])).
% 11.51/1.98  
% 11.51/1.98  fof(f69,plain,(
% 11.51/1.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.51/1.98    inference(cnf_transformation,[],[f51])).
% 11.51/1.98  
% 11.51/1.98  fof(f12,axiom,(
% 11.51/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.51/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.51/1.98  
% 11.51/1.98  fof(f31,plain,(
% 11.51/1.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.51/1.98    inference(ennf_transformation,[],[f12])).
% 11.51/1.98  
% 11.51/1.98  fof(f81,plain,(
% 11.51/1.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.51/1.98    inference(cnf_transformation,[],[f31])).
% 11.51/1.98  
% 11.51/1.98  fof(f95,plain,(
% 11.51/1.98    v1_tdlat_3(sK4)),
% 11.51/1.98    inference(cnf_transformation,[],[f63])).
% 11.51/1.98  
% 11.51/1.98  fof(f98,plain,(
% 11.51/1.98    ~v2_tex_2(sK5,sK4)),
% 11.51/1.98    inference(cnf_transformation,[],[f63])).
% 11.51/1.98  
% 11.51/1.98  fof(f84,plain,(
% 11.51/1.98    ( ! [X0,X1] : (~v2_struct_0(sK3(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.51/1.98    inference(cnf_transformation,[],[f58])).
% 11.51/1.98  
% 11.51/1.98  fof(f85,plain,(
% 11.51/1.98    ( ! [X0,X1] : (m1_pre_topc(sK3(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.51/1.98    inference(cnf_transformation,[],[f58])).
% 11.51/1.98  
% 11.51/1.98  fof(f14,axiom,(
% 11.51/1.98    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 11.51/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.51/1.98  
% 11.51/1.98  fof(f22,plain,(
% 11.51/1.98    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 11.51/1.98    inference(pure_predicate_removal,[],[f14])).
% 11.51/1.98  
% 11.51/1.98  fof(f23,plain,(
% 11.51/1.98    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v1_tdlat_3(X1)))),
% 11.51/1.98    inference(pure_predicate_removal,[],[f22])).
% 11.51/1.98  
% 11.51/1.98  fof(f34,plain,(
% 11.51/1.98    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.51/1.98    inference(ennf_transformation,[],[f23])).
% 11.51/1.98  
% 11.51/1.98  fof(f35,plain,(
% 11.51/1.98    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.51/1.98    inference(flattening,[],[f34])).
% 11.51/1.98  
% 11.51/1.98  fof(f83,plain,(
% 11.51/1.98    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.51/1.98    inference(cnf_transformation,[],[f35])).
% 11.51/1.98  
% 11.51/1.98  fof(f13,axiom,(
% 11.51/1.98    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 11.51/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.51/1.98  
% 11.51/1.98  fof(f32,plain,(
% 11.51/1.98    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 11.51/1.98    inference(ennf_transformation,[],[f13])).
% 11.51/1.98  
% 11.51/1.98  fof(f33,plain,(
% 11.51/1.98    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 11.51/1.98    inference(flattening,[],[f32])).
% 11.51/1.98  
% 11.51/1.98  fof(f82,plain,(
% 11.51/1.98    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 11.51/1.98    inference(cnf_transformation,[],[f33])).
% 11.51/1.98  
% 11.51/1.98  fof(f16,axiom,(
% 11.51/1.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 11.51/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.51/1.98  
% 11.51/1.98  fof(f38,plain,(
% 11.51/1.98    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 11.51/1.98    inference(ennf_transformation,[],[f16])).
% 11.51/1.98  
% 11.51/1.98  fof(f39,plain,(
% 11.51/1.98    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 11.51/1.98    inference(flattening,[],[f38])).
% 11.51/1.98  
% 11.51/1.98  fof(f59,plain,(
% 11.51/1.98    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 11.51/1.98    inference(nnf_transformation,[],[f39])).
% 11.51/1.98  
% 11.51/1.98  fof(f88,plain,(
% 11.51/1.98    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.51/1.98    inference(cnf_transformation,[],[f59])).
% 11.51/1.98  
% 11.51/1.98  fof(f101,plain,(
% 11.51/1.98    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.51/1.98    inference(equality_resolution,[],[f88])).
% 11.51/1.98  
% 11.51/1.98  fof(f5,axiom,(
% 11.51/1.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 11.51/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.51/1.98  
% 11.51/1.98  fof(f72,plain,(
% 11.51/1.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 11.51/1.98    inference(cnf_transformation,[],[f5])).
% 11.51/1.98  
% 11.51/1.98  fof(f4,axiom,(
% 11.51/1.98    ! [X0] : k2_subset_1(X0) = X0),
% 11.51/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.51/1.98  
% 11.51/1.98  fof(f71,plain,(
% 11.51/1.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 11.51/1.98    inference(cnf_transformation,[],[f4])).
% 11.51/1.98  
% 11.51/1.98  fof(f8,axiom,(
% 11.51/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 11.51/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.51/1.98  
% 11.51/1.98  fof(f28,plain,(
% 11.51/1.98    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 11.51/1.98    inference(ennf_transformation,[],[f8])).
% 11.51/1.98  
% 11.51/1.98  fof(f75,plain,(
% 11.51/1.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.51/1.98    inference(cnf_transformation,[],[f28])).
% 11.51/1.98  
% 11.51/1.98  fof(f6,axiom,(
% 11.51/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 11.51/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.51/1.98  
% 11.51/1.98  fof(f27,plain,(
% 11.51/1.98    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 11.51/1.98    inference(ennf_transformation,[],[f6])).
% 11.51/1.98  
% 11.51/1.98  fof(f73,plain,(
% 11.51/1.98    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.51/1.98    inference(cnf_transformation,[],[f27])).
% 11.51/1.98  
% 11.51/1.98  fof(f76,plain,(
% 11.51/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.51/1.98    inference(cnf_transformation,[],[f54])).
% 11.51/1.98  
% 11.51/1.98  fof(f18,axiom,(
% 11.51/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 11.51/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.51/1.98  
% 11.51/1.98  fof(f42,plain,(
% 11.51/1.98    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v2_tex_2(X2,X0) & ~v2_tex_2(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.51/1.98    inference(ennf_transformation,[],[f18])).
% 11.51/1.98  
% 11.51/1.98  fof(f43,plain,(
% 11.51/1.98    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v2_tex_2(X2,X0) & ~v2_tex_2(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.51/1.98    inference(flattening,[],[f42])).
% 11.51/1.98  
% 11.51/1.98  fof(f91,plain,(
% 11.51/1.98    ( ! [X2,X0,X1] : (v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.51/1.98    inference(cnf_transformation,[],[f43])).
% 11.51/1.98  
% 11.51/1.98  fof(f17,axiom,(
% 11.51/1.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X0) = X1 => (v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)))))),
% 11.51/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.51/1.98  
% 11.51/1.98  fof(f40,plain,(
% 11.51/1.98    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 11.51/1.98    inference(ennf_transformation,[],[f17])).
% 11.51/1.98  
% 11.51/1.98  fof(f41,plain,(
% 11.51/1.98    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 11.51/1.98    inference(flattening,[],[f40])).
% 11.51/1.98  
% 11.51/1.98  fof(f60,plain,(
% 11.51/1.98    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_tdlat_3(X0)) & (v1_tdlat_3(X0) | ~v2_tex_2(X1,X0))) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 11.51/1.98    inference(nnf_transformation,[],[f41])).
% 11.51/1.98  
% 11.51/1.98  fof(f90,plain,(
% 11.51/1.98    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_tdlat_3(X0) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.51/1.98    inference(cnf_transformation,[],[f60])).
% 11.51/1.98  
% 11.51/1.98  fof(f103,plain,(
% 11.51/1.98    ( ! [X0] : (v2_tex_2(u1_struct_0(X0),X0) | ~v1_tdlat_3(X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.51/1.98    inference(equality_resolution,[],[f90])).
% 11.51/1.98  
% 11.51/1.98  cnf(c_30,negated_conjecture,
% 11.51/1.98      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 11.51/1.98      inference(cnf_transformation,[],[f97]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1349,plain,
% 11.51/1.98      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_20,plain,
% 11.51/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.51/1.98      | v2_struct_0(X1)
% 11.51/1.98      | ~ l1_pre_topc(X1)
% 11.51/1.98      | v1_xboole_0(X0)
% 11.51/1.98      | u1_struct_0(sK3(X1,X0)) = X0 ),
% 11.51/1.98      inference(cnf_transformation,[],[f86]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1357,plain,
% 11.51/1.98      ( u1_struct_0(sK3(X0,X1)) = X1
% 11.51/1.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.51/1.98      | v2_struct_0(X0) = iProver_top
% 11.51/1.98      | l1_pre_topc(X0) != iProver_top
% 11.51/1.98      | v1_xboole_0(X1) = iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_3143,plain,
% 11.51/1.98      ( u1_struct_0(sK3(sK4,sK5)) = sK5
% 11.51/1.98      | v2_struct_0(sK4) = iProver_top
% 11.51/1.98      | l1_pre_topc(sK4) != iProver_top
% 11.51/1.98      | v1_xboole_0(sK5) = iProver_top ),
% 11.51/1.98      inference(superposition,[status(thm)],[c_1349,c_1357]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_34,negated_conjecture,
% 11.51/1.98      ( ~ v2_struct_0(sK4) ),
% 11.51/1.98      inference(cnf_transformation,[],[f93]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_35,plain,
% 11.51/1.98      ( v2_struct_0(sK4) != iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_31,negated_conjecture,
% 11.51/1.98      ( l1_pre_topc(sK4) ),
% 11.51/1.98      inference(cnf_transformation,[],[f96]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_38,plain,
% 11.51/1.98      ( l1_pre_topc(sK4) = iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_6687,plain,
% 11.51/1.98      ( u1_struct_0(sK3(sK4,sK5)) = sK5
% 11.51/1.98      | v1_xboole_0(sK5) = iProver_top ),
% 11.51/1.98      inference(global_propositional_subsumption,
% 11.51/1.98                [status(thm)],
% 11.51/1.98                [c_3143,c_35,c_38]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1348,plain,
% 11.51/1.98      ( l1_pre_topc(sK4) = iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_15,plain,
% 11.51/1.98      ( ~ l1_pre_topc(X0) | v1_xboole_0(sK2(X0)) ),
% 11.51/1.98      inference(cnf_transformation,[],[f80]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1362,plain,
% 11.51/1.98      ( l1_pre_topc(X0) != iProver_top
% 11.51/1.98      | v1_xboole_0(sK2(X0)) = iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1,plain,
% 11.51/1.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.51/1.98      inference(cnf_transformation,[],[f65]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1371,plain,
% 11.51/1.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.51/1.98      | r1_tarski(X0,X1) = iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_5,plain,
% 11.51/1.98      ( r1_tarski(X0,X0) ),
% 11.51/1.98      inference(cnf_transformation,[],[f100]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1368,plain,
% 11.51/1.98      ( r1_tarski(X0,X0) = iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_14,plain,
% 11.51/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.51/1.98      | ~ r2_hidden(X2,X0)
% 11.51/1.98      | ~ v1_xboole_0(X1) ),
% 11.51/1.98      inference(cnf_transformation,[],[f78]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_12,plain,
% 11.51/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.51/1.98      inference(cnf_transformation,[],[f77]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_215,plain,
% 11.51/1.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.51/1.98      inference(prop_impl,[status(thm)],[c_12]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_216,plain,
% 11.51/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.51/1.98      inference(renaming,[status(thm)],[c_215]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_277,plain,
% 11.51/1.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 11.51/1.98      inference(bin_hyper_res,[status(thm)],[c_14,c_216]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1342,plain,
% 11.51/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.51/1.98      | r1_tarski(X1,X2) != iProver_top
% 11.51/1.98      | v1_xboole_0(X2) != iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_277]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_5081,plain,
% 11.51/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.51/1.98      | v1_xboole_0(X1) != iProver_top ),
% 11.51/1.98      inference(superposition,[status(thm)],[c_1368,c_1342]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_5352,plain,
% 11.51/1.98      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 11.51/1.98      inference(superposition,[status(thm)],[c_1371,c_5081]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_3,plain,
% 11.51/1.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 11.51/1.98      inference(cnf_transformation,[],[f69]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1369,plain,
% 11.51/1.98      ( X0 = X1
% 11.51/1.98      | r1_tarski(X1,X0) != iProver_top
% 11.51/1.98      | r1_tarski(X0,X1) != iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_5369,plain,
% 11.51/1.98      ( X0 = X1
% 11.51/1.98      | r1_tarski(X0,X1) != iProver_top
% 11.51/1.98      | v1_xboole_0(X1) != iProver_top ),
% 11.51/1.98      inference(superposition,[status(thm)],[c_5352,c_1369]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_5575,plain,
% 11.51/1.98      ( X0 = X1
% 11.51/1.98      | v1_xboole_0(X1) != iProver_top
% 11.51/1.98      | v1_xboole_0(X0) != iProver_top ),
% 11.51/1.98      inference(superposition,[status(thm)],[c_5352,c_5369]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_39063,plain,
% 11.51/1.98      ( sK2(X0) = X1
% 11.51/1.98      | l1_pre_topc(X0) != iProver_top
% 11.51/1.98      | v1_xboole_0(X1) != iProver_top ),
% 11.51/1.98      inference(superposition,[status(thm)],[c_1362,c_5575]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_39414,plain,
% 11.51/1.98      ( sK2(sK4) = X0 | v1_xboole_0(X0) != iProver_top ),
% 11.51/1.98      inference(superposition,[status(thm)],[c_1348,c_39063]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_40018,plain,
% 11.51/1.98      ( u1_struct_0(sK3(sK4,sK5)) = sK5 | sK2(sK4) = sK5 ),
% 11.51/1.98      inference(superposition,[status(thm)],[c_6687,c_39414]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_17,plain,
% 11.51/1.98      ( ~ m1_pre_topc(X0,X1)
% 11.51/1.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.51/1.98      | ~ l1_pre_topc(X1) ),
% 11.51/1.98      inference(cnf_transformation,[],[f81]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1360,plain,
% 11.51/1.98      ( m1_pre_topc(X0,X1) != iProver_top
% 11.51/1.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.51/1.98      | l1_pre_topc(X1) != iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_40655,plain,
% 11.51/1.98      ( sK2(sK4) = sK5
% 11.51/1.98      | m1_pre_topc(sK3(sK4,sK5),X0) != iProver_top
% 11.51/1.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 11.51/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.51/1.98      inference(superposition,[status(thm)],[c_40018,c_1360]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_32,negated_conjecture,
% 11.51/1.98      ( v1_tdlat_3(sK4) ),
% 11.51/1.98      inference(cnf_transformation,[],[f95]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_37,plain,
% 11.51/1.98      ( v1_tdlat_3(sK4) = iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_29,negated_conjecture,
% 11.51/1.98      ( ~ v2_tex_2(sK5,sK4) ),
% 11.51/1.98      inference(cnf_transformation,[],[f98]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_40,plain,
% 11.51/1.98      ( v2_tex_2(sK5,sK4) != iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_22,plain,
% 11.51/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.51/1.98      | v2_struct_0(X1)
% 11.51/1.98      | ~ v2_struct_0(sK3(X1,X0))
% 11.51/1.98      | ~ l1_pre_topc(X1)
% 11.51/1.98      | v1_xboole_0(X0) ),
% 11.51/1.98      inference(cnf_transformation,[],[f84]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1355,plain,
% 11.51/1.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.51/1.98      | v2_struct_0(X1) = iProver_top
% 11.51/1.98      | v2_struct_0(sK3(X1,X0)) != iProver_top
% 11.51/1.98      | l1_pre_topc(X1) != iProver_top
% 11.51/1.98      | v1_xboole_0(X0) = iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_2814,plain,
% 11.51/1.98      ( v2_struct_0(sK3(sK4,sK5)) != iProver_top
% 11.51/1.98      | v2_struct_0(sK4) = iProver_top
% 11.51/1.98      | l1_pre_topc(sK4) != iProver_top
% 11.51/1.98      | v1_xboole_0(sK5) = iProver_top ),
% 11.51/1.98      inference(superposition,[status(thm)],[c_1349,c_1355]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_6132,plain,
% 11.51/1.98      ( v2_struct_0(sK3(sK4,sK5)) != iProver_top
% 11.51/1.98      | v1_xboole_0(sK5) = iProver_top ),
% 11.51/1.98      inference(global_propositional_subsumption,
% 11.51/1.98                [status(thm)],
% 11.51/1.98                [c_2814,c_35,c_38]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_21,plain,
% 11.51/1.98      ( m1_pre_topc(sK3(X0,X1),X0)
% 11.51/1.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.51/1.98      | v2_struct_0(X0)
% 11.51/1.98      | ~ l1_pre_topc(X0)
% 11.51/1.98      | v1_xboole_0(X1) ),
% 11.51/1.98      inference(cnf_transformation,[],[f85]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1356,plain,
% 11.51/1.98      ( m1_pre_topc(sK3(X0,X1),X0) = iProver_top
% 11.51/1.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.51/1.98      | v2_struct_0(X0) = iProver_top
% 11.51/1.98      | l1_pre_topc(X0) != iProver_top
% 11.51/1.98      | v1_xboole_0(X1) = iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_3478,plain,
% 11.51/1.98      ( m1_pre_topc(sK3(sK4,sK5),sK4) = iProver_top
% 11.51/1.98      | v2_struct_0(sK4) = iProver_top
% 11.51/1.98      | l1_pre_topc(sK4) != iProver_top
% 11.51/1.98      | v1_xboole_0(sK5) = iProver_top ),
% 11.51/1.98      inference(superposition,[status(thm)],[c_1349,c_1356]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_7171,plain,
% 11.51/1.98      ( m1_pre_topc(sK3(sK4,sK5),sK4) = iProver_top
% 11.51/1.98      | v1_xboole_0(sK5) = iProver_top ),
% 11.51/1.98      inference(global_propositional_subsumption,
% 11.51/1.98                [status(thm)],
% 11.51/1.98                [c_3478,c_35,c_38]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_19,plain,
% 11.51/1.98      ( ~ m1_pre_topc(X0,X1)
% 11.51/1.98      | v2_struct_0(X1)
% 11.51/1.98      | ~ v1_tdlat_3(X1)
% 11.51/1.98      | v1_tdlat_3(X0)
% 11.51/1.98      | ~ v2_pre_topc(X1)
% 11.51/1.98      | ~ l1_pre_topc(X1) ),
% 11.51/1.98      inference(cnf_transformation,[],[f83]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1358,plain,
% 11.51/1.98      ( m1_pre_topc(X0,X1) != iProver_top
% 11.51/1.98      | v2_struct_0(X1) = iProver_top
% 11.51/1.98      | v1_tdlat_3(X1) != iProver_top
% 11.51/1.98      | v1_tdlat_3(X0) = iProver_top
% 11.51/1.98      | v2_pre_topc(X1) != iProver_top
% 11.51/1.98      | l1_pre_topc(X1) != iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_18,plain,
% 11.51/1.98      ( ~ v1_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 11.51/1.98      inference(cnf_transformation,[],[f82]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1359,plain,
% 11.51/1.98      ( v1_tdlat_3(X0) != iProver_top
% 11.51/1.98      | v2_pre_topc(X0) = iProver_top
% 11.51/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1518,plain,
% 11.51/1.98      ( m1_pre_topc(X0,X1) != iProver_top
% 11.51/1.98      | v2_struct_0(X1) = iProver_top
% 11.51/1.98      | v1_tdlat_3(X1) != iProver_top
% 11.51/1.98      | v1_tdlat_3(X0) = iProver_top
% 11.51/1.98      | l1_pre_topc(X1) != iProver_top ),
% 11.51/1.98      inference(forward_subsumption_resolution,
% 11.51/1.98                [status(thm)],
% 11.51/1.98                [c_1358,c_1359]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_7177,plain,
% 11.51/1.98      ( v2_struct_0(sK4) = iProver_top
% 11.51/1.98      | v1_tdlat_3(sK3(sK4,sK5)) = iProver_top
% 11.51/1.98      | v1_tdlat_3(sK4) != iProver_top
% 11.51/1.98      | l1_pre_topc(sK4) != iProver_top
% 11.51/1.98      | v1_xboole_0(sK5) = iProver_top ),
% 11.51/1.98      inference(superposition,[status(thm)],[c_7171,c_1518]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1707,plain,
% 11.51/1.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.51/1.98      | ~ r1_tarski(X0,u1_struct_0(X1)) ),
% 11.51/1.98      inference(instantiation,[status(thm)],[c_12]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_10442,plain,
% 11.51/1.98      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 11.51/1.98      | ~ r1_tarski(sK5,u1_struct_0(X0)) ),
% 11.51/1.98      inference(instantiation,[status(thm)],[c_1707]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_10443,plain,
% 11.51/1.98      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 11.51/1.98      | r1_tarski(sK5,u1_struct_0(X0)) != iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_10442]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_3624,plain,
% 11.51/1.98      ( ~ r2_hidden(sK0(X0,u1_struct_0(X1)),X0)
% 11.51/1.98      | ~ r1_tarski(X0,X2)
% 11.51/1.98      | ~ v1_xboole_0(X2) ),
% 11.51/1.98      inference(instantiation,[status(thm)],[c_277]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_6402,plain,
% 11.51/1.98      ( ~ r2_hidden(sK0(X0,u1_struct_0(X1)),X0)
% 11.51/1.98      | ~ r1_tarski(X0,sK5)
% 11.51/1.98      | ~ v1_xboole_0(sK5) ),
% 11.51/1.98      inference(instantiation,[status(thm)],[c_3624]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_10659,plain,
% 11.51/1.98      ( ~ r2_hidden(sK0(sK5,u1_struct_0(X0)),sK5)
% 11.51/1.98      | ~ r1_tarski(sK5,sK5)
% 11.51/1.98      | ~ v1_xboole_0(sK5) ),
% 11.51/1.98      inference(instantiation,[status(thm)],[c_6402]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_10661,plain,
% 11.51/1.98      ( r2_hidden(sK0(sK5,u1_struct_0(X0)),sK5) != iProver_top
% 11.51/1.98      | r1_tarski(sK5,sK5) != iProver_top
% 11.51/1.98      | v1_xboole_0(sK5) != iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_10659]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_10660,plain,
% 11.51/1.98      ( r1_tarski(sK5,sK5) ),
% 11.51/1.98      inference(instantiation,[status(thm)],[c_5]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_10665,plain,
% 11.51/1.98      ( r1_tarski(sK5,sK5) = iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_10660]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1881,plain,
% 11.51/1.98      ( r2_hidden(sK0(X0,u1_struct_0(X1)),X0)
% 11.51/1.98      | r1_tarski(X0,u1_struct_0(X1)) ),
% 11.51/1.98      inference(instantiation,[status(thm)],[c_1]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_24314,plain,
% 11.51/1.98      ( r2_hidden(sK0(sK5,u1_struct_0(X0)),sK5)
% 11.51/1.98      | r1_tarski(sK5,u1_struct_0(X0)) ),
% 11.51/1.98      inference(instantiation,[status(thm)],[c_1881]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_24315,plain,
% 11.51/1.98      ( r2_hidden(sK0(sK5,u1_struct_0(X0)),sK5) = iProver_top
% 11.51/1.98      | r1_tarski(sK5,u1_struct_0(X0)) = iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_24314]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_23,plain,
% 11.51/1.98      ( v2_tex_2(u1_struct_0(X0),X1)
% 11.51/1.98      | ~ m1_pre_topc(X0,X1)
% 11.51/1.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.51/1.98      | v2_struct_0(X1)
% 11.51/1.98      | v2_struct_0(X0)
% 11.51/1.98      | ~ v1_tdlat_3(X0)
% 11.51/1.98      | ~ l1_pre_topc(X1) ),
% 11.51/1.98      inference(cnf_transformation,[],[f101]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_350,plain,
% 11.51/1.98      ( ~ m1_pre_topc(X0,X1)
% 11.51/1.98      | v2_tex_2(u1_struct_0(X0),X1)
% 11.51/1.98      | v2_struct_0(X1)
% 11.51/1.98      | v2_struct_0(X0)
% 11.51/1.98      | ~ v1_tdlat_3(X0)
% 11.51/1.98      | ~ l1_pre_topc(X1) ),
% 11.51/1.98      inference(global_propositional_subsumption,
% 11.51/1.98                [status(thm)],
% 11.51/1.98                [c_23,c_17]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_351,plain,
% 11.51/1.98      ( v2_tex_2(u1_struct_0(X0),X1)
% 11.51/1.98      | ~ m1_pre_topc(X0,X1)
% 11.51/1.98      | v2_struct_0(X0)
% 11.51/1.98      | v2_struct_0(X1)
% 11.51/1.98      | ~ v1_tdlat_3(X0)
% 11.51/1.98      | ~ l1_pre_topc(X1) ),
% 11.51/1.98      inference(renaming,[status(thm)],[c_350]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1340,plain,
% 11.51/1.98      ( v2_tex_2(u1_struct_0(X0),X1) = iProver_top
% 11.51/1.98      | m1_pre_topc(X0,X1) != iProver_top
% 11.51/1.98      | v2_struct_0(X0) = iProver_top
% 11.51/1.98      | v2_struct_0(X1) = iProver_top
% 11.51/1.98      | v1_tdlat_3(X0) != iProver_top
% 11.51/1.98      | l1_pre_topc(X1) != iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_351]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_40658,plain,
% 11.51/1.98      ( sK2(sK4) = sK5
% 11.51/1.98      | v2_tex_2(sK5,X0) = iProver_top
% 11.51/1.98      | m1_pre_topc(sK3(sK4,sK5),X0) != iProver_top
% 11.51/1.98      | v2_struct_0(X0) = iProver_top
% 11.51/1.98      | v2_struct_0(sK3(sK4,sK5)) = iProver_top
% 11.51/1.98      | v1_tdlat_3(sK3(sK4,sK5)) != iProver_top
% 11.51/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.51/1.98      inference(superposition,[status(thm)],[c_40018,c_1340]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_41419,plain,
% 11.51/1.98      ( sK2(sK4) = sK5
% 11.51/1.98      | v2_tex_2(sK5,sK4) = iProver_top
% 11.51/1.98      | m1_pre_topc(sK3(sK4,sK5),sK4) != iProver_top
% 11.51/1.98      | v2_struct_0(sK3(sK4,sK5)) = iProver_top
% 11.51/1.98      | v2_struct_0(sK4) = iProver_top
% 11.51/1.98      | v1_tdlat_3(sK3(sK4,sK5)) != iProver_top
% 11.51/1.98      | l1_pre_topc(sK4) != iProver_top ),
% 11.51/1.98      inference(instantiation,[status(thm)],[c_40658]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_41961,plain,
% 11.51/1.98      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 11.51/1.98      | sK2(sK4) = sK5 ),
% 11.51/1.98      inference(global_propositional_subsumption,
% 11.51/1.98                [status(thm)],
% 11.51/1.98                [c_40655,c_35,c_37,c_38,c_40,c_6132,c_7171,c_7177,
% 11.51/1.98                 c_10443,c_10661,c_10665,c_24315,c_41419]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_41962,plain,
% 11.51/1.98      ( sK2(sK4) = sK5
% 11.51/1.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 11.51/1.98      inference(renaming,[status(thm)],[c_41961]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_41970,plain,
% 11.51/1.98      ( u1_struct_0(sK3(X0,sK5)) = sK5
% 11.51/1.98      | sK2(sK4) = sK5
% 11.51/1.98      | v2_struct_0(X0) = iProver_top
% 11.51/1.98      | l1_pre_topc(X0) != iProver_top
% 11.51/1.98      | v1_xboole_0(sK5) = iProver_top ),
% 11.51/1.98      inference(superposition,[status(thm)],[c_41962,c_1357]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_42931,plain,
% 11.51/1.98      ( sK2(sK4) = sK5 | v1_xboole_0(sK5) = iProver_top ),
% 11.51/1.98      inference(global_propositional_subsumption,
% 11.51/1.98                [status(thm)],
% 11.51/1.98                [c_41970,c_35,c_37,c_38,c_40,c_6132,c_7171,c_7177,
% 11.51/1.98                 c_41419]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_42937,plain,
% 11.51/1.98      ( sK2(sK4) = sK5 ),
% 11.51/1.98      inference(forward_subsumption_resolution,
% 11.51/1.98                [status(thm)],
% 11.51/1.98                [c_42931,c_39414]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_8,plain,
% 11.51/1.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 11.51/1.98      inference(cnf_transformation,[],[f72]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1366,plain,
% 11.51/1.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_7,plain,
% 11.51/1.98      ( k2_subset_1(X0) = X0 ),
% 11.51/1.98      inference(cnf_transformation,[],[f71]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1391,plain,
% 11.51/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.51/1.98      inference(light_normalisation,[status(thm)],[c_1366,c_7]) ).
% 11.51/1.98  
% 11.51/1.98  cnf(c_1364,plain,
% 11.51/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.51/1.98      | r1_tarski(X0,X1) != iProver_top ),
% 11.51/1.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_11,plain,
% 11.51/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.51/1.99      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 11.51/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_274,plain,
% 11.51/1.99      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 11.51/1.99      inference(bin_hyper_res,[status(thm)],[c_11,c_216]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1343,plain,
% 11.51/1.99      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 11.51/1.99      | r1_tarski(X2,X0) != iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_274]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_5372,plain,
% 11.51/1.99      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 11.51/1.99      | v1_xboole_0(X2) != iProver_top ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_5352,c_1343]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_26700,plain,
% 11.51/1.99      ( k9_subset_1(X0,X1,sK2(X2)) = k3_xboole_0(X1,sK2(X2))
% 11.51/1.99      | l1_pre_topc(X2) != iProver_top ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_1362,c_5372]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_26767,plain,
% 11.51/1.99      ( k9_subset_1(X0,X1,sK2(sK4)) = k3_xboole_0(X1,sK2(sK4)) ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_1348,c_26700]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_4572,plain,
% 11.51/1.99      ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_1368,c_1343]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_9,plain,
% 11.51/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.51/1.99      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 11.51/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_273,plain,
% 11.51/1.99      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 11.51/1.99      | ~ r1_tarski(X2,X0) ),
% 11.51/1.99      inference(bin_hyper_res,[status(thm)],[c_9,c_216]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1344,plain,
% 11.51/1.99      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 11.51/1.99      | r1_tarski(X2,X0) != iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_273]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_4732,plain,
% 11.51/1.99      ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top
% 11.51/1.99      | r1_tarski(X1,X1) != iProver_top ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_4572,c_1344]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_14173,plain,
% 11.51/1.99      ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top ),
% 11.51/1.99      inference(forward_subsumption_resolution,
% 11.51/1.99                [status(thm)],
% 11.51/1.99                [c_4732,c_1368]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_13,plain,
% 11.51/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.51/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1363,plain,
% 11.51/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.51/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_14177,plain,
% 11.51/1.99      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_14173,c_1363]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_14430,plain,
% 11.51/1.99      ( k3_xboole_0(X0,X1) = X1 | v1_xboole_0(X1) != iProver_top ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_14177,c_5369]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_18836,plain,
% 11.51/1.99      ( k3_xboole_0(X0,sK2(X1)) = sK2(X1)
% 11.51/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_1362,c_14430]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_19107,plain,
% 11.51/1.99      ( k3_xboole_0(X0,sK2(sK4)) = sK2(sK4) ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_1348,c_18836]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_26768,plain,
% 11.51/1.99      ( k9_subset_1(X0,X1,sK2(sK4)) = sK2(sK4) ),
% 11.51/1.99      inference(demodulation,[status(thm)],[c_26767,c_19107]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_28,plain,
% 11.51/1.99      ( ~ v2_tex_2(X0,X1)
% 11.51/1.99      | v2_tex_2(k9_subset_1(u1_struct_0(X1),X0,X2),X1)
% 11.51/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.51/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.51/1.99      | ~ l1_pre_topc(X1) ),
% 11.51/1.99      inference(cnf_transformation,[],[f91]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1351,plain,
% 11.51/1.99      ( v2_tex_2(X0,X1) != iProver_top
% 11.51/1.99      | v2_tex_2(k9_subset_1(u1_struct_0(X1),X0,X2),X1) = iProver_top
% 11.51/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.51/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.51/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_28322,plain,
% 11.51/1.99      ( v2_tex_2(X0,X1) != iProver_top
% 11.51/1.99      | v2_tex_2(sK2(sK4),X1) = iProver_top
% 11.51/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.51/1.99      | m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.51/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_26768,c_1351]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_28774,plain,
% 11.51/1.99      ( v2_tex_2(X0,X1) != iProver_top
% 11.51/1.99      | v2_tex_2(sK2(sK4),X1) = iProver_top
% 11.51/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.51/1.99      | r1_tarski(sK2(sK4),u1_struct_0(X1)) != iProver_top
% 11.51/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_1364,c_28322]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_28801,plain,
% 11.51/1.99      ( v2_tex_2(u1_struct_0(X0),X0) != iProver_top
% 11.51/1.99      | v2_tex_2(sK2(sK4),X0) = iProver_top
% 11.51/1.99      | r1_tarski(sK2(sK4),u1_struct_0(X0)) != iProver_top
% 11.51/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_1391,c_28774]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_42944,plain,
% 11.51/1.99      ( v2_tex_2(u1_struct_0(X0),X0) != iProver_top
% 11.51/1.99      | v2_tex_2(sK5,X0) = iProver_top
% 11.51/1.99      | r1_tarski(sK5,u1_struct_0(X0)) != iProver_top
% 11.51/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.51/1.99      inference(demodulation,[status(thm)],[c_42937,c_28801]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_43047,plain,
% 11.51/1.99      ( v2_tex_2(u1_struct_0(sK4),sK4) != iProver_top
% 11.51/1.99      | v2_tex_2(sK5,sK4) = iProver_top
% 11.51/1.99      | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top
% 11.51/1.99      | l1_pre_topc(sK4) != iProver_top ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_42944]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1778,plain,
% 11.51/1.99      ( r1_tarski(sK5,u1_struct_0(sK4)) ),
% 11.51/1.99      inference(resolution,[status(thm)],[c_13,c_30]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1779,plain,
% 11.51/1.99      ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_1778]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_25,plain,
% 11.51/1.99      ( v2_tex_2(u1_struct_0(X0),X0)
% 11.51/1.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 11.51/1.99      | v2_struct_0(X0)
% 11.51/1.99      | ~ v1_tdlat_3(X0)
% 11.51/1.99      | ~ l1_pre_topc(X0) ),
% 11.51/1.99      inference(cnf_transformation,[],[f103]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1354,plain,
% 11.51/1.99      ( v2_tex_2(u1_struct_0(X0),X0) = iProver_top
% 11.51/1.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.51/1.99      | v2_struct_0(X0) = iProver_top
% 11.51/1.99      | v1_tdlat_3(X0) != iProver_top
% 11.51/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1507,plain,
% 11.51/1.99      ( v2_tex_2(u1_struct_0(X0),X0) = iProver_top
% 11.51/1.99      | v2_struct_0(X0) = iProver_top
% 11.51/1.99      | v1_tdlat_3(X0) != iProver_top
% 11.51/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.51/1.99      inference(forward_subsumption_resolution,
% 11.51/1.99                [status(thm)],
% 11.51/1.99                [c_1354,c_1391]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1584,plain,
% 11.51/1.99      ( v2_tex_2(u1_struct_0(sK4),sK4) = iProver_top
% 11.51/1.99      | v2_struct_0(sK4) = iProver_top
% 11.51/1.99      | v1_tdlat_3(sK4) != iProver_top
% 11.51/1.99      | l1_pre_topc(sK4) != iProver_top ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_1507]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(contradiction,plain,
% 11.51/1.99      ( $false ),
% 11.51/1.99      inference(minisat,
% 11.51/1.99                [status(thm)],
% 11.51/1.99                [c_43047,c_1779,c_1584,c_40,c_38,c_37,c_35]) ).
% 11.51/1.99  
% 11.51/1.99  
% 11.51/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.51/1.99  
% 11.51/1.99  ------                               Statistics
% 11.51/1.99  
% 11.51/1.99  ------ Selected
% 11.51/1.99  
% 11.51/1.99  total_time:                             1.277
% 11.51/1.99  
%------------------------------------------------------------------------------
