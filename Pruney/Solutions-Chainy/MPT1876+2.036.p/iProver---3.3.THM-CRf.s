%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:54 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  238 (6092 expanded)
%              Number of clauses        :  150 (1570 expanded)
%              Number of leaves         :   23 (1377 expanded)
%              Depth                    :   32
%              Number of atoms          :  912 (41988 expanded)
%              Number of equality atoms :  300 (2860 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f57,plain,(
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

fof(f56,plain,
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

fof(f58,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f55,f57,f56])).

fof(f91,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f90,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f58])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f52,plain,(
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

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f52])).

fof(f83,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f86,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f88,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f89,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

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
    inference(nnf_transformation,[],[f20])).

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
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f79,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f59,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f60,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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

fof(f31,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f76,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f74,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f72,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f92,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_27,negated_conjecture,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_4985,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_4984,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_21,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4991,plain,
    ( u1_struct_0(sK2(X0,X1)) = X1
    | v2_tex_2(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6431,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4984,c_4991])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_34,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_35,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_37,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_38,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6481,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6431,c_34,c_35,c_37,c_38])).

cnf(c_6487,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4985,c_6481])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_5003,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_5000,plain,
    ( r1_tarski(k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4992,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6325,plain,
    ( k1_tarski(X0) = X1
    | r2_hidden(X0,X1) != iProver_top
    | v1_zfmisc_1(X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k1_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5000,c_4992])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_92,plain,
    ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_102,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8047,plain,
    ( k1_tarski(X0) = X1
    | r2_hidden(X0,X1) != iProver_top
    | v1_zfmisc_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6325,c_92,c_102])).

cnf(c_8057,plain,
    ( k1_tarski(sK1(X0,X1)) = X0
    | r1_tarski(X0,X1) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5003,c_8047])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_5006,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8056,plain,
    ( k1_tarski(sK0(X0)) = X0
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5006,c_8047])).

cnf(c_8248,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | k1_tarski(sK0(sK4)) = sK4
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6487,c_8056])).

cnf(c_8270,plain,
    ( v1_xboole_0(sK4)
    | u1_struct_0(sK2(sK3,sK4)) = sK4
    | k1_tarski(sK0(sK4)) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8248])).

cnf(c_8429,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8248,c_29,c_8270])).

cnf(c_8430,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | k1_tarski(sK0(sK4)) = sK4 ),
    inference(renaming,[status(thm)],[c_8429])).

cnf(c_25,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_4987,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8434,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v2_tex_2(k6_domain_1(sK4,X0),sK2(sK3,sK4)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2(sK3,sK4))) != iProver_top
    | v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v2_pre_topc(sK2(sK3,sK4)) != iProver_top
    | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8430,c_4987])).

cnf(c_17,plain,
    ( v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_15,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_192,plain,
    ( ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_15])).

cnf(c_193,plain,
    ( v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_192])).

cnf(c_11,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_13,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_448,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_11,c_13])).

cnf(c_466,plain,
    ( v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_193,c_448])).

cnf(c_4978,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v2_tdlat_3(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_8435,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | v2_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top
    | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8430,c_4978])).

cnf(c_40,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_268,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(prop_impl,[status(thm)],[c_27])).

cnf(c_269,plain,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(renaming,[status(thm)],[c_268])).

cnf(c_1061,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_269])).

cnf(c_1062,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(sK2(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1061])).

cnf(c_1064,plain,
    ( ~ v2_struct_0(sK2(sK3,sK4))
    | v1_zfmisc_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1062,c_33,c_32,c_30,c_29,c_28])).

cnf(c_1066,plain,
    ( v2_struct_0(sK2(sK3,sK4)) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1064])).

cnf(c_23,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_tdlat_3(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1075,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_tdlat_3(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_269])).

cnf(c_1076,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | v1_tdlat_3(sK2(sK3,sK4))
    | ~ v2_pre_topc(sK3)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1075])).

cnf(c_1078,plain,
    ( v1_tdlat_3(sK2(sK3,sK4))
    | v1_zfmisc_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1076,c_33,c_32,c_30,c_29,c_28])).

cnf(c_1080,plain,
    ( v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1078])).

cnf(c_22,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_4990,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_pre_topc(sK2(X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6763,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4984,c_4990])).

cnf(c_2242,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK2(X1,X0),X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_2243,plain,
    ( ~ v2_tex_2(sK4,X0)
    | m1_pre_topc(sK2(X0,sK4),X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK4)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_2242])).

cnf(c_2247,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | m1_pre_topc(sK2(X0,sK4),X0)
    | ~ v2_tex_2(sK4,X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2243,c_29])).

cnf(c_2248,plain,
    ( ~ v2_tex_2(sK4,X0)
    | m1_pre_topc(sK2(X0,sK4),X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_2247])).

cnf(c_2249,plain,
    ( k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK3))
    | v2_tex_2(sK4,X0) != iProver_top
    | m1_pre_topc(sK2(X0,sK4),X0) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2248])).

cnf(c_2251,plain,
    ( k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
    | v2_tex_2(sK4,sK3) != iProver_top
    | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2249])).

cnf(c_4156,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6924,plain,
    ( k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_4156])).

cnf(c_6929,plain,
    ( k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_6924])).

cnf(c_7129,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6763,c_34,c_35,c_37,c_2251,c_6929])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4995,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7135,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | l1_pre_topc(sK2(sK3,sK4)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7129,c_4995])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1305,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X2)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_1306,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_1305])).

cnf(c_4977,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_tdlat_3(X1) != iProver_top
    | v2_tdlat_3(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1306])).

cnf(c_7136,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_tdlat_3(sK2(sK3,sK4)) = iProver_top
    | v2_tdlat_3(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7129,c_4977])).

cnf(c_31,negated_conjecture,
    ( v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,plain,
    ( v2_tdlat_3(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7227,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v2_tdlat_3(sK2(sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7136,c_34,c_36,c_37])).

cnf(c_8768,plain,
    ( v1_zfmisc_1(sK4) = iProver_top
    | k1_tarski(sK0(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8435,c_34,c_36,c_37,c_40,c_1066,c_1080,c_7135,c_7136])).

cnf(c_8769,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_8768])).

cnf(c_8774,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_8769,c_8056])).

cnf(c_8777,plain,
    ( k1_tarski(sK0(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8434,c_38,c_8774])).

cnf(c_7,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4999,plain,
    ( r1_tarski(k1_tarski(X0),X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8793,plain,
    ( r1_tarski(sK4,X0) != iProver_top
    | r2_hidden(sK0(sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8777,c_4999])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_4998,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9098,plain,
    ( m1_subset_1(sK0(sK4),X0) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8793,c_4998])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4994,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9306,plain,
    ( k6_domain_1(X0,sK0(sK4)) = k1_tarski(sK0(sK4))
    | r1_tarski(sK4,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9098,c_4994])).

cnf(c_9310,plain,
    ( k6_domain_1(X0,sK0(sK4)) = sK4
    | r1_tarski(sK4,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9306,c_8777])).

cnf(c_5005,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9097,plain,
    ( r1_tarski(sK4,X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8793,c_5005])).

cnf(c_10575,plain,
    ( r1_tarski(sK4,X0) != iProver_top
    | k6_domain_1(X0,sK0(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9310,c_9097])).

cnf(c_10576,plain,
    ( k6_domain_1(X0,sK0(sK4)) = sK4
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10575])).

cnf(c_10583,plain,
    ( k6_domain_1(X0,sK0(sK4)) = sK4
    | k1_tarski(sK1(sK4,X0)) = sK4
    | v1_zfmisc_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8057,c_10576])).

cnf(c_26,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_41,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4996,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5504,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4984,c_4996])).

cnf(c_5667,plain,
    ( r2_hidden(sK0(sK4),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5668,plain,
    ( r2_hidden(sK0(sK4),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5667])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5835,plain,
    ( ~ r1_tarski(sK4,X0)
    | r2_hidden(sK0(sK4),X0)
    | ~ r2_hidden(sK0(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6273,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(X0))
    | r2_hidden(sK0(sK4),u1_struct_0(X0))
    | ~ r2_hidden(sK0(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_5835])).

cnf(c_6277,plain,
    ( r1_tarski(sK4,u1_struct_0(X0)) != iProver_top
    | r2_hidden(sK0(sK4),u1_struct_0(X0)) = iProver_top
    | r2_hidden(sK0(sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6273])).

cnf(c_6279,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(sK4),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(sK4),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6277])).

cnf(c_5274,plain,
    ( m1_subset_1(X0,u1_struct_0(X1))
    | ~ r2_hidden(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_8294,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(X0))
    | ~ r2_hidden(sK0(sK4),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_5274])).

cnf(c_8295,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
    | r2_hidden(sK0(sK4),u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8294])).

cnf(c_8297,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8295])).

cnf(c_5002,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5942,plain,
    ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5504,c_5002])).

cnf(c_6094,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5942,c_4998])).

cnf(c_6613,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
    | r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6094,c_4994])).

cnf(c_6093,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5942,c_5005])).

cnf(c_7351,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6613,c_6093])).

cnf(c_7352,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_7351])).

cnf(c_7359,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4))
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5006,c_7352])).

cnf(c_7374,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7359,c_38])).

cnf(c_8781,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = sK4 ),
    inference(demodulation,[status(thm)],[c_8777,c_7374])).

cnf(c_9627,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8781,c_4987])).

cnf(c_12985,plain,
    ( v1_zfmisc_1(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10583,c_34,c_35,c_37,c_38,c_41,c_5504,c_5668,c_6279,c_8297,c_9627])).

cnf(c_12990,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_6487,c_12985])).

cnf(c_13057,plain,
    ( v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | v2_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top
    | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12990,c_4978])).

cnf(c_4988,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK2(X1,X0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6649,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v2_struct_0(sK2(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4984,c_4988])).

cnf(c_2182,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_2183,plain,
    ( ~ v2_tex_2(sK4,X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK2(X0,sK4))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK4)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_2182])).

cnf(c_2187,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_struct_0(sK2(X0,sK4))
    | v2_struct_0(X0)
    | ~ v2_tex_2(sK4,X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2183,c_29])).

cnf(c_2188,plain,
    ( ~ v2_tex_2(sK4,X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK2(X0,sK4))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_2187])).

cnf(c_2189,plain,
    ( k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK3))
    | v2_tex_2(sK4,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2(X0,sK4)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2188])).

cnf(c_2191,plain,
    ( k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
    | v2_tex_2(sK4,sK3) != iProver_top
    | v2_struct_0(sK2(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2189])).

cnf(c_7122,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v2_struct_0(sK2(sK3,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6649,c_34,c_35,c_37,c_2191,c_6929])).

cnf(c_4989,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_tdlat_3(sK2(X1,X0)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6359,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4984,c_4989])).

cnf(c_6474,plain,
    ( v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
    | v2_tex_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6359,c_34,c_35,c_37,c_38])).

cnf(c_6475,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6474])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13057,c_9627,c_8297,c_7227,c_7135,c_7122,c_6475,c_6279,c_5668,c_5504,c_41,c_38,c_37,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.37/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/0.98  
% 3.37/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.37/0.98  
% 3.37/0.98  ------  iProver source info
% 3.37/0.98  
% 3.37/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.37/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.37/0.98  git: non_committed_changes: false
% 3.37/0.98  git: last_make_outside_of_git: false
% 3.37/0.98  
% 3.37/0.98  ------ 
% 3.37/0.98  
% 3.37/0.98  ------ Input Options
% 3.37/0.98  
% 3.37/0.98  --out_options                           all
% 3.37/0.98  --tptp_safe_out                         true
% 3.37/0.98  --problem_path                          ""
% 3.37/0.98  --include_path                          ""
% 3.37/0.98  --clausifier                            res/vclausify_rel
% 3.37/0.98  --clausifier_options                    --mode clausify
% 3.37/0.98  --stdin                                 false
% 3.37/0.98  --stats_out                             all
% 3.37/0.98  
% 3.37/0.98  ------ General Options
% 3.37/0.98  
% 3.37/0.98  --fof                                   false
% 3.37/0.98  --time_out_real                         305.
% 3.37/0.98  --time_out_virtual                      -1.
% 3.37/0.98  --symbol_type_check                     false
% 3.37/0.98  --clausify_out                          false
% 3.37/0.98  --sig_cnt_out                           false
% 3.37/0.98  --trig_cnt_out                          false
% 3.37/0.98  --trig_cnt_out_tolerance                1.
% 3.37/0.98  --trig_cnt_out_sk_spl                   false
% 3.37/0.98  --abstr_cl_out                          false
% 3.37/0.98  
% 3.37/0.98  ------ Global Options
% 3.37/0.98  
% 3.37/0.98  --schedule                              default
% 3.37/0.98  --add_important_lit                     false
% 3.37/0.98  --prop_solver_per_cl                    1000
% 3.37/0.98  --min_unsat_core                        false
% 3.37/0.98  --soft_assumptions                      false
% 3.37/0.98  --soft_lemma_size                       3
% 3.37/0.98  --prop_impl_unit_size                   0
% 3.37/0.98  --prop_impl_unit                        []
% 3.37/0.98  --share_sel_clauses                     true
% 3.37/0.98  --reset_solvers                         false
% 3.37/0.98  --bc_imp_inh                            [conj_cone]
% 3.37/0.98  --conj_cone_tolerance                   3.
% 3.37/0.98  --extra_neg_conj                        none
% 3.37/0.98  --large_theory_mode                     true
% 3.37/0.98  --prolific_symb_bound                   200
% 3.37/0.98  --lt_threshold                          2000
% 3.37/0.98  --clause_weak_htbl                      true
% 3.37/0.98  --gc_record_bc_elim                     false
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing Options
% 3.37/0.98  
% 3.37/0.98  --preprocessing_flag                    true
% 3.37/0.98  --time_out_prep_mult                    0.1
% 3.37/0.98  --splitting_mode                        input
% 3.37/0.98  --splitting_grd                         true
% 3.37/0.98  --splitting_cvd                         false
% 3.37/0.98  --splitting_cvd_svl                     false
% 3.37/0.98  --splitting_nvd                         32
% 3.37/0.98  --sub_typing                            true
% 3.37/0.98  --prep_gs_sim                           true
% 3.37/0.98  --prep_unflatten                        true
% 3.37/0.98  --prep_res_sim                          true
% 3.37/0.98  --prep_upred                            true
% 3.37/0.98  --prep_sem_filter                       exhaustive
% 3.37/0.98  --prep_sem_filter_out                   false
% 3.37/0.98  --pred_elim                             true
% 3.37/0.98  --res_sim_input                         true
% 3.37/0.98  --eq_ax_congr_red                       true
% 3.37/0.98  --pure_diseq_elim                       true
% 3.37/0.98  --brand_transform                       false
% 3.37/0.98  --non_eq_to_eq                          false
% 3.37/0.98  --prep_def_merge                        true
% 3.37/0.98  --prep_def_merge_prop_impl              false
% 3.37/0.98  --prep_def_merge_mbd                    true
% 3.37/0.98  --prep_def_merge_tr_red                 false
% 3.37/0.98  --prep_def_merge_tr_cl                  false
% 3.37/0.98  --smt_preprocessing                     true
% 3.37/0.98  --smt_ac_axioms                         fast
% 3.37/0.98  --preprocessed_out                      false
% 3.37/0.98  --preprocessed_stats                    false
% 3.37/0.98  
% 3.37/0.98  ------ Abstraction refinement Options
% 3.37/0.98  
% 3.37/0.98  --abstr_ref                             []
% 3.37/0.98  --abstr_ref_prep                        false
% 3.37/0.98  --abstr_ref_until_sat                   false
% 3.37/0.98  --abstr_ref_sig_restrict                funpre
% 3.37/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/0.98  --abstr_ref_under                       []
% 3.37/0.98  
% 3.37/0.98  ------ SAT Options
% 3.37/0.98  
% 3.37/0.98  --sat_mode                              false
% 3.37/0.98  --sat_fm_restart_options                ""
% 3.37/0.98  --sat_gr_def                            false
% 3.37/0.98  --sat_epr_types                         true
% 3.37/0.98  --sat_non_cyclic_types                  false
% 3.37/0.98  --sat_finite_models                     false
% 3.37/0.98  --sat_fm_lemmas                         false
% 3.37/0.98  --sat_fm_prep                           false
% 3.37/0.98  --sat_fm_uc_incr                        true
% 3.37/0.98  --sat_out_model                         small
% 3.37/0.98  --sat_out_clauses                       false
% 3.37/0.98  
% 3.37/0.98  ------ QBF Options
% 3.37/0.98  
% 3.37/0.98  --qbf_mode                              false
% 3.37/0.98  --qbf_elim_univ                         false
% 3.37/0.98  --qbf_dom_inst                          none
% 3.37/0.98  --qbf_dom_pre_inst                      false
% 3.37/0.98  --qbf_sk_in                             false
% 3.37/0.98  --qbf_pred_elim                         true
% 3.37/0.98  --qbf_split                             512
% 3.37/0.98  
% 3.37/0.98  ------ BMC1 Options
% 3.37/0.98  
% 3.37/0.98  --bmc1_incremental                      false
% 3.37/0.98  --bmc1_axioms                           reachable_all
% 3.37/0.98  --bmc1_min_bound                        0
% 3.37/0.98  --bmc1_max_bound                        -1
% 3.37/0.98  --bmc1_max_bound_default                -1
% 3.37/0.98  --bmc1_symbol_reachability              true
% 3.37/0.98  --bmc1_property_lemmas                  false
% 3.37/0.98  --bmc1_k_induction                      false
% 3.37/0.98  --bmc1_non_equiv_states                 false
% 3.37/0.98  --bmc1_deadlock                         false
% 3.37/0.98  --bmc1_ucm                              false
% 3.37/0.98  --bmc1_add_unsat_core                   none
% 3.37/0.98  --bmc1_unsat_core_children              false
% 3.37/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/0.98  --bmc1_out_stat                         full
% 3.37/0.98  --bmc1_ground_init                      false
% 3.37/0.98  --bmc1_pre_inst_next_state              false
% 3.37/0.98  --bmc1_pre_inst_state                   false
% 3.37/0.98  --bmc1_pre_inst_reach_state             false
% 3.37/0.98  --bmc1_out_unsat_core                   false
% 3.37/0.98  --bmc1_aig_witness_out                  false
% 3.37/0.98  --bmc1_verbose                          false
% 3.37/0.98  --bmc1_dump_clauses_tptp                false
% 3.37/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.37/0.98  --bmc1_dump_file                        -
% 3.37/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.37/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.37/0.98  --bmc1_ucm_extend_mode                  1
% 3.37/0.98  --bmc1_ucm_init_mode                    2
% 3.37/0.98  --bmc1_ucm_cone_mode                    none
% 3.37/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.37/0.98  --bmc1_ucm_relax_model                  4
% 3.37/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.37/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/0.98  --bmc1_ucm_layered_model                none
% 3.37/0.98  --bmc1_ucm_max_lemma_size               10
% 3.37/0.98  
% 3.37/0.98  ------ AIG Options
% 3.37/0.98  
% 3.37/0.98  --aig_mode                              false
% 3.37/0.98  
% 3.37/0.98  ------ Instantiation Options
% 3.37/0.98  
% 3.37/0.98  --instantiation_flag                    true
% 3.37/0.98  --inst_sos_flag                         false
% 3.37/0.98  --inst_sos_phase                        true
% 3.37/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/0.98  --inst_lit_sel_side                     num_symb
% 3.37/0.98  --inst_solver_per_active                1400
% 3.37/0.98  --inst_solver_calls_frac                1.
% 3.37/0.98  --inst_passive_queue_type               priority_queues
% 3.37/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/0.98  --inst_passive_queues_freq              [25;2]
% 3.37/0.98  --inst_dismatching                      true
% 3.37/0.98  --inst_eager_unprocessed_to_passive     true
% 3.37/0.98  --inst_prop_sim_given                   true
% 3.37/0.98  --inst_prop_sim_new                     false
% 3.37/0.98  --inst_subs_new                         false
% 3.37/0.98  --inst_eq_res_simp                      false
% 3.37/0.98  --inst_subs_given                       false
% 3.37/0.98  --inst_orphan_elimination               true
% 3.37/0.98  --inst_learning_loop_flag               true
% 3.37/0.98  --inst_learning_start                   3000
% 3.37/0.98  --inst_learning_factor                  2
% 3.37/0.98  --inst_start_prop_sim_after_learn       3
% 3.37/0.98  --inst_sel_renew                        solver
% 3.37/0.98  --inst_lit_activity_flag                true
% 3.37/0.98  --inst_restr_to_given                   false
% 3.37/0.98  --inst_activity_threshold               500
% 3.37/0.98  --inst_out_proof                        true
% 3.37/0.98  
% 3.37/0.98  ------ Resolution Options
% 3.37/0.98  
% 3.37/0.98  --resolution_flag                       true
% 3.37/0.98  --res_lit_sel                           adaptive
% 3.37/0.98  --res_lit_sel_side                      none
% 3.37/0.98  --res_ordering                          kbo
% 3.37/0.98  --res_to_prop_solver                    active
% 3.37/0.98  --res_prop_simpl_new                    false
% 3.37/0.98  --res_prop_simpl_given                  true
% 3.37/0.98  --res_passive_queue_type                priority_queues
% 3.37/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/0.98  --res_passive_queues_freq               [15;5]
% 3.37/0.98  --res_forward_subs                      full
% 3.37/0.98  --res_backward_subs                     full
% 3.37/0.98  --res_forward_subs_resolution           true
% 3.37/0.98  --res_backward_subs_resolution          true
% 3.37/0.98  --res_orphan_elimination                true
% 3.37/0.98  --res_time_limit                        2.
% 3.37/0.98  --res_out_proof                         true
% 3.37/0.98  
% 3.37/0.98  ------ Superposition Options
% 3.37/0.98  
% 3.37/0.98  --superposition_flag                    true
% 3.37/0.98  --sup_passive_queue_type                priority_queues
% 3.37/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.37/0.98  --demod_completeness_check              fast
% 3.37/0.98  --demod_use_ground                      true
% 3.37/0.98  --sup_to_prop_solver                    passive
% 3.37/0.98  --sup_prop_simpl_new                    true
% 3.37/0.98  --sup_prop_simpl_given                  true
% 3.37/0.98  --sup_fun_splitting                     false
% 3.37/0.98  --sup_smt_interval                      50000
% 3.37/0.98  
% 3.37/0.98  ------ Superposition Simplification Setup
% 3.37/0.98  
% 3.37/0.98  --sup_indices_passive                   []
% 3.37/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_full_bw                           [BwDemod]
% 3.37/0.98  --sup_immed_triv                        [TrivRules]
% 3.37/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_immed_bw_main                     []
% 3.37/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.98  
% 3.37/0.98  ------ Combination Options
% 3.37/0.98  
% 3.37/0.98  --comb_res_mult                         3
% 3.37/0.98  --comb_sup_mult                         2
% 3.37/0.98  --comb_inst_mult                        10
% 3.37/0.98  
% 3.37/0.98  ------ Debug Options
% 3.37/0.98  
% 3.37/0.98  --dbg_backtrace                         false
% 3.37/0.98  --dbg_dump_prop_clauses                 false
% 3.37/0.98  --dbg_dump_prop_clauses_file            -
% 3.37/0.98  --dbg_out_stat                          false
% 3.37/0.98  ------ Parsing...
% 3.37/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/0.98  ------ Proving...
% 3.37/0.98  ------ Problem Properties 
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  clauses                                 30
% 3.37/0.98  conjectures                             8
% 3.37/0.98  EPR                                     14
% 3.37/0.98  Horn                                    18
% 3.37/0.98  unary                                   7
% 3.37/0.98  binary                                  11
% 3.37/0.98  lits                                    89
% 3.37/0.98  lits eq                                 3
% 3.37/0.98  fd_pure                                 0
% 3.37/0.98  fd_pseudo                               0
% 3.37/0.98  fd_cond                                 0
% 3.37/0.98  fd_pseudo_cond                          1
% 3.37/0.98  AC symbols                              0
% 3.37/0.98  
% 3.37/0.98  ------ Schedule dynamic 5 is on 
% 3.37/0.98  
% 3.37/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  ------ 
% 3.37/0.98  Current options:
% 3.37/0.98  ------ 
% 3.37/0.98  
% 3.37/0.98  ------ Input Options
% 3.37/0.98  
% 3.37/0.98  --out_options                           all
% 3.37/0.98  --tptp_safe_out                         true
% 3.37/0.98  --problem_path                          ""
% 3.37/0.98  --include_path                          ""
% 3.37/0.98  --clausifier                            res/vclausify_rel
% 3.37/0.98  --clausifier_options                    --mode clausify
% 3.37/0.98  --stdin                                 false
% 3.37/0.98  --stats_out                             all
% 3.37/0.98  
% 3.37/0.98  ------ General Options
% 3.37/0.98  
% 3.37/0.98  --fof                                   false
% 3.37/0.98  --time_out_real                         305.
% 3.37/0.98  --time_out_virtual                      -1.
% 3.37/0.98  --symbol_type_check                     false
% 3.37/0.98  --clausify_out                          false
% 3.37/0.98  --sig_cnt_out                           false
% 3.37/0.98  --trig_cnt_out                          false
% 3.37/0.98  --trig_cnt_out_tolerance                1.
% 3.37/0.98  --trig_cnt_out_sk_spl                   false
% 3.37/0.98  --abstr_cl_out                          false
% 3.37/0.98  
% 3.37/0.98  ------ Global Options
% 3.37/0.98  
% 3.37/0.98  --schedule                              default
% 3.37/0.98  --add_important_lit                     false
% 3.37/0.98  --prop_solver_per_cl                    1000
% 3.37/0.98  --min_unsat_core                        false
% 3.37/0.98  --soft_assumptions                      false
% 3.37/0.98  --soft_lemma_size                       3
% 3.37/0.98  --prop_impl_unit_size                   0
% 3.37/0.98  --prop_impl_unit                        []
% 3.37/0.98  --share_sel_clauses                     true
% 3.37/0.98  --reset_solvers                         false
% 3.37/0.98  --bc_imp_inh                            [conj_cone]
% 3.37/0.98  --conj_cone_tolerance                   3.
% 3.37/0.99  --extra_neg_conj                        none
% 3.37/0.99  --large_theory_mode                     true
% 3.37/0.99  --prolific_symb_bound                   200
% 3.37/0.99  --lt_threshold                          2000
% 3.37/0.99  --clause_weak_htbl                      true
% 3.37/0.99  --gc_record_bc_elim                     false
% 3.37/0.99  
% 3.37/0.99  ------ Preprocessing Options
% 3.37/0.99  
% 3.37/0.99  --preprocessing_flag                    true
% 3.37/0.99  --time_out_prep_mult                    0.1
% 3.37/0.99  --splitting_mode                        input
% 3.37/0.99  --splitting_grd                         true
% 3.37/0.99  --splitting_cvd                         false
% 3.37/0.99  --splitting_cvd_svl                     false
% 3.37/0.99  --splitting_nvd                         32
% 3.37/0.99  --sub_typing                            true
% 3.37/0.99  --prep_gs_sim                           true
% 3.37/0.99  --prep_unflatten                        true
% 3.37/0.99  --prep_res_sim                          true
% 3.37/0.99  --prep_upred                            true
% 3.37/0.99  --prep_sem_filter                       exhaustive
% 3.37/0.99  --prep_sem_filter_out                   false
% 3.37/0.99  --pred_elim                             true
% 3.37/0.99  --res_sim_input                         true
% 3.37/0.99  --eq_ax_congr_red                       true
% 3.37/0.99  --pure_diseq_elim                       true
% 3.37/0.99  --brand_transform                       false
% 3.37/0.99  --non_eq_to_eq                          false
% 3.37/0.99  --prep_def_merge                        true
% 3.37/0.99  --prep_def_merge_prop_impl              false
% 3.37/0.99  --prep_def_merge_mbd                    true
% 3.37/0.99  --prep_def_merge_tr_red                 false
% 3.37/0.99  --prep_def_merge_tr_cl                  false
% 3.37/0.99  --smt_preprocessing                     true
% 3.37/0.99  --smt_ac_axioms                         fast
% 3.37/0.99  --preprocessed_out                      false
% 3.37/0.99  --preprocessed_stats                    false
% 3.37/0.99  
% 3.37/0.99  ------ Abstraction refinement Options
% 3.37/0.99  
% 3.37/0.99  --abstr_ref                             []
% 3.37/0.99  --abstr_ref_prep                        false
% 3.37/0.99  --abstr_ref_until_sat                   false
% 3.37/0.99  --abstr_ref_sig_restrict                funpre
% 3.37/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/0.99  --abstr_ref_under                       []
% 3.37/0.99  
% 3.37/0.99  ------ SAT Options
% 3.37/0.99  
% 3.37/0.99  --sat_mode                              false
% 3.37/0.99  --sat_fm_restart_options                ""
% 3.37/0.99  --sat_gr_def                            false
% 3.37/0.99  --sat_epr_types                         true
% 3.37/0.99  --sat_non_cyclic_types                  false
% 3.37/0.99  --sat_finite_models                     false
% 3.37/0.99  --sat_fm_lemmas                         false
% 3.37/0.99  --sat_fm_prep                           false
% 3.37/0.99  --sat_fm_uc_incr                        true
% 3.37/0.99  --sat_out_model                         small
% 3.37/0.99  --sat_out_clauses                       false
% 3.37/0.99  
% 3.37/0.99  ------ QBF Options
% 3.37/0.99  
% 3.37/0.99  --qbf_mode                              false
% 3.37/0.99  --qbf_elim_univ                         false
% 3.37/0.99  --qbf_dom_inst                          none
% 3.37/0.99  --qbf_dom_pre_inst                      false
% 3.37/0.99  --qbf_sk_in                             false
% 3.37/0.99  --qbf_pred_elim                         true
% 3.37/0.99  --qbf_split                             512
% 3.37/0.99  
% 3.37/0.99  ------ BMC1 Options
% 3.37/0.99  
% 3.37/0.99  --bmc1_incremental                      false
% 3.37/0.99  --bmc1_axioms                           reachable_all
% 3.37/0.99  --bmc1_min_bound                        0
% 3.37/0.99  --bmc1_max_bound                        -1
% 3.37/0.99  --bmc1_max_bound_default                -1
% 3.37/0.99  --bmc1_symbol_reachability              true
% 3.37/0.99  --bmc1_property_lemmas                  false
% 3.37/0.99  --bmc1_k_induction                      false
% 3.37/0.99  --bmc1_non_equiv_states                 false
% 3.37/0.99  --bmc1_deadlock                         false
% 3.37/0.99  --bmc1_ucm                              false
% 3.37/0.99  --bmc1_add_unsat_core                   none
% 3.37/0.99  --bmc1_unsat_core_children              false
% 3.37/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/0.99  --bmc1_out_stat                         full
% 3.37/0.99  --bmc1_ground_init                      false
% 3.37/0.99  --bmc1_pre_inst_next_state              false
% 3.37/0.99  --bmc1_pre_inst_state                   false
% 3.37/0.99  --bmc1_pre_inst_reach_state             false
% 3.37/0.99  --bmc1_out_unsat_core                   false
% 3.37/0.99  --bmc1_aig_witness_out                  false
% 3.37/0.99  --bmc1_verbose                          false
% 3.37/0.99  --bmc1_dump_clauses_tptp                false
% 3.37/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.37/0.99  --bmc1_dump_file                        -
% 3.37/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.37/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.37/0.99  --bmc1_ucm_extend_mode                  1
% 3.37/0.99  --bmc1_ucm_init_mode                    2
% 3.37/0.99  --bmc1_ucm_cone_mode                    none
% 3.37/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.37/0.99  --bmc1_ucm_relax_model                  4
% 3.37/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.37/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/0.99  --bmc1_ucm_layered_model                none
% 3.37/0.99  --bmc1_ucm_max_lemma_size               10
% 3.37/0.99  
% 3.37/0.99  ------ AIG Options
% 3.37/0.99  
% 3.37/0.99  --aig_mode                              false
% 3.37/0.99  
% 3.37/0.99  ------ Instantiation Options
% 3.37/0.99  
% 3.37/0.99  --instantiation_flag                    true
% 3.37/0.99  --inst_sos_flag                         false
% 3.37/0.99  --inst_sos_phase                        true
% 3.37/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/0.99  --inst_lit_sel_side                     none
% 3.37/0.99  --inst_solver_per_active                1400
% 3.37/0.99  --inst_solver_calls_frac                1.
% 3.37/0.99  --inst_passive_queue_type               priority_queues
% 3.37/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/0.99  --inst_passive_queues_freq              [25;2]
% 3.37/0.99  --inst_dismatching                      true
% 3.37/0.99  --inst_eager_unprocessed_to_passive     true
% 3.37/0.99  --inst_prop_sim_given                   true
% 3.37/0.99  --inst_prop_sim_new                     false
% 3.37/0.99  --inst_subs_new                         false
% 3.37/0.99  --inst_eq_res_simp                      false
% 3.37/0.99  --inst_subs_given                       false
% 3.37/0.99  --inst_orphan_elimination               true
% 3.37/0.99  --inst_learning_loop_flag               true
% 3.37/0.99  --inst_learning_start                   3000
% 3.37/0.99  --inst_learning_factor                  2
% 3.37/0.99  --inst_start_prop_sim_after_learn       3
% 3.37/0.99  --inst_sel_renew                        solver
% 3.37/0.99  --inst_lit_activity_flag                true
% 3.37/0.99  --inst_restr_to_given                   false
% 3.37/0.99  --inst_activity_threshold               500
% 3.37/0.99  --inst_out_proof                        true
% 3.37/0.99  
% 3.37/0.99  ------ Resolution Options
% 3.37/0.99  
% 3.37/0.99  --resolution_flag                       false
% 3.37/0.99  --res_lit_sel                           adaptive
% 3.37/0.99  --res_lit_sel_side                      none
% 3.37/0.99  --res_ordering                          kbo
% 3.37/0.99  --res_to_prop_solver                    active
% 3.37/0.99  --res_prop_simpl_new                    false
% 3.37/0.99  --res_prop_simpl_given                  true
% 3.37/0.99  --res_passive_queue_type                priority_queues
% 3.37/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/0.99  --res_passive_queues_freq               [15;5]
% 3.37/0.99  --res_forward_subs                      full
% 3.37/0.99  --res_backward_subs                     full
% 3.37/0.99  --res_forward_subs_resolution           true
% 3.37/0.99  --res_backward_subs_resolution          true
% 3.37/0.99  --res_orphan_elimination                true
% 3.37/0.99  --res_time_limit                        2.
% 3.37/0.99  --res_out_proof                         true
% 3.37/0.99  
% 3.37/0.99  ------ Superposition Options
% 3.37/0.99  
% 3.37/0.99  --superposition_flag                    true
% 3.37/0.99  --sup_passive_queue_type                priority_queues
% 3.37/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.37/0.99  --demod_completeness_check              fast
% 3.37/0.99  --demod_use_ground                      true
% 3.37/0.99  --sup_to_prop_solver                    passive
% 3.37/0.99  --sup_prop_simpl_new                    true
% 3.37/0.99  --sup_prop_simpl_given                  true
% 3.37/0.99  --sup_fun_splitting                     false
% 3.37/0.99  --sup_smt_interval                      50000
% 3.37/0.99  
% 3.37/0.99  ------ Superposition Simplification Setup
% 3.37/0.99  
% 3.37/0.99  --sup_indices_passive                   []
% 3.37/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.99  --sup_full_bw                           [BwDemod]
% 3.37/0.99  --sup_immed_triv                        [TrivRules]
% 3.37/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.99  --sup_immed_bw_main                     []
% 3.37/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.99  
% 3.37/0.99  ------ Combination Options
% 3.37/0.99  
% 3.37/0.99  --comb_res_mult                         3
% 3.37/0.99  --comb_sup_mult                         2
% 3.37/0.99  --comb_inst_mult                        10
% 3.37/0.99  
% 3.37/0.99  ------ Debug Options
% 3.37/0.99  
% 3.37/0.99  --dbg_backtrace                         false
% 3.37/0.99  --dbg_dump_prop_clauses                 false
% 3.37/0.99  --dbg_dump_prop_clauses_file            -
% 3.37/0.99  --dbg_out_stat                          false
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  ------ Proving...
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  % SZS status Theorem for theBenchmark.p
% 3.37/0.99  
% 3.37/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.37/0.99  
% 3.37/0.99  fof(f17,conjecture,(
% 3.37/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f18,negated_conjecture,(
% 3.37/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.37/0.99    inference(negated_conjecture,[],[f17])).
% 3.37/0.99  
% 3.37/0.99  fof(f40,plain,(
% 3.37/0.99    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.37/0.99    inference(ennf_transformation,[],[f18])).
% 3.37/0.99  
% 3.37/0.99  fof(f41,plain,(
% 3.37/0.99    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.37/0.99    inference(flattening,[],[f40])).
% 3.37/0.99  
% 3.37/0.99  fof(f54,plain,(
% 3.37/0.99    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.37/0.99    inference(nnf_transformation,[],[f41])).
% 3.37/0.99  
% 3.37/0.99  fof(f55,plain,(
% 3.37/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.37/0.99    inference(flattening,[],[f54])).
% 3.37/0.99  
% 3.37/0.99  fof(f57,plain,(
% 3.37/0.99    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,X0)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK4))) )),
% 3.37/0.99    introduced(choice_axiom,[])).
% 3.37/0.99  
% 3.37/0.99  fof(f56,plain,(
% 3.37/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.37/0.99    introduced(choice_axiom,[])).
% 3.37/0.99  
% 3.37/0.99  fof(f58,plain,(
% 3.37/0.99    ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.37/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f55,f57,f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f91,plain,(
% 3.37/0.99    v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)),
% 3.37/0.99    inference(cnf_transformation,[],[f58])).
% 3.37/0.99  
% 3.37/0.99  fof(f90,plain,(
% 3.37/0.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.37/0.99    inference(cnf_transformation,[],[f58])).
% 3.37/0.99  
% 3.37/0.99  fof(f15,axiom,(
% 3.37/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f19,plain,(
% 3.37/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.37/0.99    inference(pure_predicate_removal,[],[f15])).
% 3.37/0.99  
% 3.37/0.99  fof(f36,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.37/0.99    inference(ennf_transformation,[],[f19])).
% 3.37/0.99  
% 3.37/0.99  fof(f37,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/0.99    inference(flattening,[],[f36])).
% 3.37/0.99  
% 3.37/0.99  fof(f52,plain,(
% 3.37/0.99    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 3.37/0.99    introduced(choice_axiom,[])).
% 3.37/0.99  
% 3.37/0.99  fof(f53,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f52])).
% 3.37/0.99  
% 3.37/0.99  fof(f83,plain,(
% 3.37/0.99    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f53])).
% 3.37/0.99  
% 3.37/0.99  fof(f85,plain,(
% 3.37/0.99    ~v2_struct_0(sK3)),
% 3.37/0.99    inference(cnf_transformation,[],[f58])).
% 3.37/0.99  
% 3.37/0.99  fof(f86,plain,(
% 3.37/0.99    v2_pre_topc(sK3)),
% 3.37/0.99    inference(cnf_transformation,[],[f58])).
% 3.37/0.99  
% 3.37/0.99  fof(f88,plain,(
% 3.37/0.99    l1_pre_topc(sK3)),
% 3.37/0.99    inference(cnf_transformation,[],[f58])).
% 3.37/0.99  
% 3.37/0.99  fof(f89,plain,(
% 3.37/0.99    ~v1_xboole_0(sK4)),
% 3.37/0.99    inference(cnf_transformation,[],[f58])).
% 3.37/0.99  
% 3.37/0.99  fof(f2,axiom,(
% 3.37/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f20,plain,(
% 3.37/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.37/0.99    inference(ennf_transformation,[],[f2])).
% 3.37/0.99  
% 3.37/0.99  fof(f46,plain,(
% 3.37/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.37/0.99    inference(nnf_transformation,[],[f20])).
% 3.37/0.99  
% 3.37/0.99  fof(f47,plain,(
% 3.37/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.37/0.99    inference(rectify,[],[f46])).
% 3.37/0.99  
% 3.37/0.99  fof(f48,plain,(
% 3.37/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.37/0.99    introduced(choice_axiom,[])).
% 3.37/0.99  
% 3.37/0.99  fof(f49,plain,(
% 3.37/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.37/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).
% 3.37/0.99  
% 3.37/0.99  fof(f62,plain,(
% 3.37/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f49])).
% 3.37/0.99  
% 3.37/0.99  fof(f4,axiom,(
% 3.37/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f50,plain,(
% 3.37/0.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.37/0.99    inference(nnf_transformation,[],[f4])).
% 3.37/0.99  
% 3.37/0.99  fof(f66,plain,(
% 3.37/0.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f50])).
% 3.37/0.99  
% 3.37/0.99  fof(f14,axiom,(
% 3.37/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f34,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 3.37/0.99    inference(ennf_transformation,[],[f14])).
% 3.37/0.99  
% 3.37/0.99  fof(f35,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.37/0.99    inference(flattening,[],[f34])).
% 3.37/0.99  
% 3.37/0.99  fof(f79,plain,(
% 3.37/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f35])).
% 3.37/0.99  
% 3.37/0.99  fof(f3,axiom,(
% 3.37/0.99    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f64,plain,(
% 3.37/0.99    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.37/0.99    inference(cnf_transformation,[],[f3])).
% 3.37/0.99  
% 3.37/0.99  fof(f1,axiom,(
% 3.37/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f42,plain,(
% 3.37/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.37/0.99    inference(nnf_transformation,[],[f1])).
% 3.37/0.99  
% 3.37/0.99  fof(f43,plain,(
% 3.37/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.37/0.99    inference(rectify,[],[f42])).
% 3.37/0.99  
% 3.37/0.99  fof(f44,plain,(
% 3.37/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.37/0.99    introduced(choice_axiom,[])).
% 3.37/0.99  
% 3.37/0.99  fof(f45,plain,(
% 3.37/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.37/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 3.37/0.99  
% 3.37/0.99  fof(f59,plain,(
% 3.37/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f45])).
% 3.37/0.99  
% 3.37/0.99  fof(f60,plain,(
% 3.37/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f45])).
% 3.37/0.99  
% 3.37/0.99  fof(f16,axiom,(
% 3.37/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f38,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.37/0.99    inference(ennf_transformation,[],[f16])).
% 3.37/0.99  
% 3.37/0.99  fof(f39,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/0.99    inference(flattening,[],[f38])).
% 3.37/0.99  
% 3.37/0.99  fof(f84,plain,(
% 3.37/0.99    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f39])).
% 3.37/0.99  
% 3.37/0.99  fof(f12,axiom,(
% 3.37/0.99    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f30,plain,(
% 3.37/0.99    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.37/0.99    inference(ennf_transformation,[],[f12])).
% 3.37/0.99  
% 3.37/0.99  fof(f31,plain,(
% 3.37/0.99    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.37/0.99    inference(flattening,[],[f30])).
% 3.37/0.99  
% 3.37/0.99  fof(f76,plain,(
% 3.37/0.99    ( ! [X0] : (v7_struct_0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f31])).
% 3.37/0.99  
% 3.37/0.99  fof(f11,axiom,(
% 3.37/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f28,plain,(
% 3.37/0.99    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.37/0.99    inference(ennf_transformation,[],[f11])).
% 3.37/0.99  
% 3.37/0.99  fof(f29,plain,(
% 3.37/0.99    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.37/0.99    inference(flattening,[],[f28])).
% 3.37/0.99  
% 3.37/0.99  fof(f74,plain,(
% 3.37/0.99    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f29])).
% 3.37/0.99  
% 3.37/0.99  fof(f7,axiom,(
% 3.37/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f22,plain,(
% 3.37/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.37/0.99    inference(ennf_transformation,[],[f7])).
% 3.37/0.99  
% 3.37/0.99  fof(f70,plain,(
% 3.37/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f22])).
% 3.37/0.99  
% 3.37/0.99  fof(f9,axiom,(
% 3.37/0.99    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f24,plain,(
% 3.37/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 3.37/0.99    inference(ennf_transformation,[],[f9])).
% 3.37/0.99  
% 3.37/0.99  fof(f25,plain,(
% 3.37/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 3.37/0.99    inference(flattening,[],[f24])).
% 3.37/0.99  
% 3.37/0.99  fof(f72,plain,(
% 3.37/0.99    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f25])).
% 3.37/0.99  
% 3.37/0.99  fof(f80,plain,(
% 3.37/0.99    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f53])).
% 3.37/0.99  
% 3.37/0.99  fof(f81,plain,(
% 3.37/0.99    ( ! [X0,X1] : (v1_tdlat_3(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f53])).
% 3.37/0.99  
% 3.37/0.99  fof(f82,plain,(
% 3.37/0.99    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f53])).
% 3.37/0.99  
% 3.37/0.99  fof(f8,axiom,(
% 3.37/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f23,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.37/0.99    inference(ennf_transformation,[],[f8])).
% 3.37/0.99  
% 3.37/0.99  fof(f71,plain,(
% 3.37/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f23])).
% 3.37/0.99  
% 3.37/0.99  fof(f13,axiom,(
% 3.37/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f32,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.37/0.99    inference(ennf_transformation,[],[f13])).
% 3.37/0.99  
% 3.37/0.99  fof(f33,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/0.99    inference(flattening,[],[f32])).
% 3.37/0.99  
% 3.37/0.99  fof(f78,plain,(
% 3.37/0.99    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f33])).
% 3.37/0.99  
% 3.37/0.99  fof(f87,plain,(
% 3.37/0.99    v2_tdlat_3(sK3)),
% 3.37/0.99    inference(cnf_transformation,[],[f58])).
% 3.37/0.99  
% 3.37/0.99  fof(f65,plain,(
% 3.37/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f50])).
% 3.37/0.99  
% 3.37/0.99  fof(f5,axiom,(
% 3.37/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f21,plain,(
% 3.37/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.37/0.99    inference(ennf_transformation,[],[f5])).
% 3.37/0.99  
% 3.37/0.99  fof(f67,plain,(
% 3.37/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f21])).
% 3.37/0.99  
% 3.37/0.99  fof(f10,axiom,(
% 3.37/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f26,plain,(
% 3.37/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.37/0.99    inference(ennf_transformation,[],[f10])).
% 3.37/0.99  
% 3.37/0.99  fof(f27,plain,(
% 3.37/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.37/0.99    inference(flattening,[],[f26])).
% 3.37/0.99  
% 3.37/0.99  fof(f73,plain,(
% 3.37/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f27])).
% 3.37/0.99  
% 3.37/0.99  fof(f92,plain,(
% 3.37/0.99    ~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)),
% 3.37/0.99    inference(cnf_transformation,[],[f58])).
% 3.37/0.99  
% 3.37/0.99  fof(f6,axiom,(
% 3.37/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f51,plain,(
% 3.37/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.37/0.99    inference(nnf_transformation,[],[f6])).
% 3.37/0.99  
% 3.37/0.99  fof(f68,plain,(
% 3.37/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.37/0.99    inference(cnf_transformation,[],[f51])).
% 3.37/0.99  
% 3.37/0.99  fof(f61,plain,(
% 3.37/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f49])).
% 3.37/0.99  
% 3.37/0.99  cnf(c_27,negated_conjecture,
% 3.37/0.99      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 3.37/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4985,plain,
% 3.37/0.99      ( v2_tex_2(sK4,sK3) = iProver_top
% 3.37/0.99      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_28,negated_conjecture,
% 3.37/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.37/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4984,plain,
% 3.37/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_21,plain,
% 3.37/0.99      ( ~ v2_tex_2(X0,X1)
% 3.37/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | v1_xboole_0(X0)
% 3.37/0.99      | u1_struct_0(sK2(X1,X0)) = X0 ),
% 3.37/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4991,plain,
% 3.37/0.99      ( u1_struct_0(sK2(X0,X1)) = X1
% 3.37/0.99      | v2_tex_2(X1,X0) != iProver_top
% 3.37/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.37/0.99      | v2_struct_0(X0) = iProver_top
% 3.37/0.99      | v2_pre_topc(X0) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top
% 3.37/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6431,plain,
% 3.37/0.99      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.37/0.99      | v2_tex_2(sK4,sK3) != iProver_top
% 3.37/0.99      | v2_struct_0(sK3) = iProver_top
% 3.37/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.37/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_4984,c_4991]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_33,negated_conjecture,
% 3.37/0.99      ( ~ v2_struct_0(sK3) ),
% 3.37/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_34,plain,
% 3.37/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_32,negated_conjecture,
% 3.37/0.99      ( v2_pre_topc(sK3) ),
% 3.37/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_35,plain,
% 3.37/0.99      ( v2_pre_topc(sK3) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_30,negated_conjecture,
% 3.37/0.99      ( l1_pre_topc(sK3) ),
% 3.37/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_37,plain,
% 3.37/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_29,negated_conjecture,
% 3.37/0.99      ( ~ v1_xboole_0(sK4) ),
% 3.37/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_38,plain,
% 3.37/0.99      ( v1_xboole_0(sK4) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6481,plain,
% 3.37/0.99      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.37/0.99      | v2_tex_2(sK4,sK3) != iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_6431,c_34,c_35,c_37,c_38]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6487,plain,
% 3.37/0.99      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.37/0.99      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_4985,c_6481]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3,plain,
% 3.37/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5003,plain,
% 3.37/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.37/0.99      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6,plain,
% 3.37/0.99      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5000,plain,
% 3.37/0.99      ( r1_tarski(k1_tarski(X0),X1) = iProver_top
% 3.37/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_20,plain,
% 3.37/0.99      ( ~ r1_tarski(X0,X1)
% 3.37/0.99      | ~ v1_zfmisc_1(X1)
% 3.37/0.99      | v1_xboole_0(X0)
% 3.37/0.99      | v1_xboole_0(X1)
% 3.37/0.99      | X1 = X0 ),
% 3.37/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4992,plain,
% 3.37/0.99      ( X0 = X1
% 3.37/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.37/0.99      | v1_zfmisc_1(X0) != iProver_top
% 3.37/0.99      | v1_xboole_0(X1) = iProver_top
% 3.37/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6325,plain,
% 3.37/0.99      ( k1_tarski(X0) = X1
% 3.37/0.99      | r2_hidden(X0,X1) != iProver_top
% 3.37/0.99      | v1_zfmisc_1(X1) != iProver_top
% 3.37/0.99      | v1_xboole_0(X1) = iProver_top
% 3.37/0.99      | v1_xboole_0(k1_tarski(X0)) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_5000,c_4992]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5,plain,
% 3.37/0.99      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 3.37/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_92,plain,
% 3.37/0.99      ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1,plain,
% 3.37/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_102,plain,
% 3.37/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.37/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8047,plain,
% 3.37/0.99      ( k1_tarski(X0) = X1
% 3.37/0.99      | r2_hidden(X0,X1) != iProver_top
% 3.37/0.99      | v1_zfmisc_1(X1) != iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_6325,c_92,c_102]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8057,plain,
% 3.37/0.99      ( k1_tarski(sK1(X0,X1)) = X0
% 3.37/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.37/0.99      | v1_zfmisc_1(X0) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_5003,c_8047]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_0,plain,
% 3.37/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5006,plain,
% 3.37/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.37/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8056,plain,
% 3.37/0.99      ( k1_tarski(sK0(X0)) = X0
% 3.37/0.99      | v1_zfmisc_1(X0) != iProver_top
% 3.37/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_5006,c_8047]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8248,plain,
% 3.37/0.99      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.37/0.99      | k1_tarski(sK0(sK4)) = sK4
% 3.37/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_6487,c_8056]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8270,plain,
% 3.37/0.99      ( v1_xboole_0(sK4)
% 3.37/0.99      | u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.37/0.99      | k1_tarski(sK0(sK4)) = sK4 ),
% 3.37/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_8248]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8429,plain,
% 3.37/0.99      ( k1_tarski(sK0(sK4)) = sK4 | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_8248,c_29,c_8270]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8430,plain,
% 3.37/0.99      ( u1_struct_0(sK2(sK3,sK4)) = sK4 | k1_tarski(sK0(sK4)) = sK4 ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_8429]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_25,plain,
% 3.37/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.37/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | ~ v2_pre_topc(X0)
% 3.37/0.99      | ~ l1_pre_topc(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4987,plain,
% 3.37/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) = iProver_top
% 3.37/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.37/0.99      | v2_struct_0(X0) = iProver_top
% 3.37/0.99      | v2_pre_topc(X0) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8434,plain,
% 3.37/0.99      ( k1_tarski(sK0(sK4)) = sK4
% 3.37/0.99      | v2_tex_2(k6_domain_1(sK4,X0),sK2(sK3,sK4)) = iProver_top
% 3.37/0.99      | m1_subset_1(X0,u1_struct_0(sK2(sK3,sK4))) != iProver_top
% 3.37/0.99      | v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 3.37/0.99      | v2_pre_topc(sK2(sK3,sK4)) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_8430,c_4987]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_17,plain,
% 3.37/0.99      ( v2_struct_0(X0)
% 3.37/0.99      | ~ v1_tdlat_3(X0)
% 3.37/0.99      | ~ v2_tdlat_3(X0)
% 3.37/0.99      | ~ v2_pre_topc(X0)
% 3.37/0.99      | v7_struct_0(X0)
% 3.37/0.99      | ~ l1_pre_topc(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_15,plain,
% 3.37/0.99      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_192,plain,
% 3.37/0.99      ( ~ v2_tdlat_3(X0)
% 3.37/0.99      | ~ v1_tdlat_3(X0)
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | v7_struct_0(X0)
% 3.37/0.99      | ~ l1_pre_topc(X0) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_17,c_15]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_193,plain,
% 3.37/0.99      ( v2_struct_0(X0)
% 3.37/0.99      | ~ v1_tdlat_3(X0)
% 3.37/0.99      | ~ v2_tdlat_3(X0)
% 3.37/0.99      | v7_struct_0(X0)
% 3.37/0.99      | ~ l1_pre_topc(X0) ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_192]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_11,plain,
% 3.37/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_13,plain,
% 3.37/0.99      ( ~ v7_struct_0(X0)
% 3.37/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.37/0.99      | ~ l1_struct_0(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_448,plain,
% 3.37/0.99      ( ~ v7_struct_0(X0)
% 3.37/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.37/0.99      | ~ l1_pre_topc(X0) ),
% 3.37/0.99      inference(resolution,[status(thm)],[c_11,c_13]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_466,plain,
% 3.37/0.99      ( v2_struct_0(X0)
% 3.37/0.99      | ~ v1_tdlat_3(X0)
% 3.37/0.99      | ~ v2_tdlat_3(X0)
% 3.37/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.37/0.99      | ~ l1_pre_topc(X0) ),
% 3.37/0.99      inference(resolution,[status(thm)],[c_193,c_448]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4978,plain,
% 3.37/0.99      ( v2_struct_0(X0) = iProver_top
% 3.37/0.99      | v1_tdlat_3(X0) != iProver_top
% 3.37/0.99      | v2_tdlat_3(X0) != iProver_top
% 3.37/0.99      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8435,plain,
% 3.37/0.99      ( k1_tarski(sK0(sK4)) = sK4
% 3.37/0.99      | v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 3.37/0.99      | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 3.37/0.99      | v2_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 3.37/0.99      | v1_zfmisc_1(sK4) = iProver_top
% 3.37/0.99      | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_8430,c_4978]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_40,plain,
% 3.37/0.99      ( v2_tex_2(sK4,sK3) = iProver_top
% 3.37/0.99      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_24,plain,
% 3.37/0.99      ( ~ v2_tex_2(X0,X1)
% 3.37/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v2_struct_0(sK2(X1,X0))
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | v1_xboole_0(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_268,plain,
% 3.37/0.99      ( v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3) ),
% 3.37/0.99      inference(prop_impl,[status(thm)],[c_27]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_269,plain,
% 3.37/0.99      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_268]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1061,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v2_struct_0(sK2(X1,X0))
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | v1_zfmisc_1(sK4)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | v1_xboole_0(X0)
% 3.37/0.99      | sK3 != X1
% 3.37/0.99      | sK4 != X0 ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_269]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1062,plain,
% 3.37/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.37/0.99      | ~ v2_struct_0(sK2(sK3,sK4))
% 3.37/0.99      | v2_struct_0(sK3)
% 3.37/0.99      | ~ v2_pre_topc(sK3)
% 3.37/0.99      | v1_zfmisc_1(sK4)
% 3.37/0.99      | ~ l1_pre_topc(sK3)
% 3.37/0.99      | v1_xboole_0(sK4) ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_1061]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1064,plain,
% 3.37/0.99      ( ~ v2_struct_0(sK2(sK3,sK4)) | v1_zfmisc_1(sK4) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_1062,c_33,c_32,c_30,c_29,c_28]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1066,plain,
% 3.37/0.99      ( v2_struct_0(sK2(sK3,sK4)) != iProver_top
% 3.37/0.99      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_1064]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_23,plain,
% 3.37/0.99      ( ~ v2_tex_2(X0,X1)
% 3.37/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | v1_tdlat_3(sK2(X1,X0))
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | v1_xboole_0(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1075,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | v1_tdlat_3(sK2(X1,X0))
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | v1_zfmisc_1(sK4)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | v1_xboole_0(X0)
% 3.37/0.99      | sK3 != X1
% 3.37/0.99      | sK4 != X0 ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_269]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1076,plain,
% 3.37/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.37/0.99      | v2_struct_0(sK3)
% 3.37/0.99      | v1_tdlat_3(sK2(sK3,sK4))
% 3.37/0.99      | ~ v2_pre_topc(sK3)
% 3.37/0.99      | v1_zfmisc_1(sK4)
% 3.37/0.99      | ~ l1_pre_topc(sK3)
% 3.37/0.99      | v1_xboole_0(sK4) ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_1075]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1078,plain,
% 3.37/0.99      ( v1_tdlat_3(sK2(sK3,sK4)) | v1_zfmisc_1(sK4) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_1076,c_33,c_32,c_30,c_29,c_28]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1080,plain,
% 3.37/0.99      ( v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
% 3.37/0.99      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_1078]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_22,plain,
% 3.37/0.99      ( ~ v2_tex_2(X0,X1)
% 3.37/0.99      | m1_pre_topc(sK2(X1,X0),X1)
% 3.37/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | v1_xboole_0(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4990,plain,
% 3.37/0.99      ( v2_tex_2(X0,X1) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK2(X1,X0),X1) = iProver_top
% 3.37/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.37/0.99      | v2_struct_0(X1) = iProver_top
% 3.37/0.99      | v2_pre_topc(X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top
% 3.37/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6763,plain,
% 3.37/0.99      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
% 3.37/0.99      | v2_struct_0(sK3) = iProver_top
% 3.37/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.37/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_4984,c_4990]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2242,plain,
% 3.37/0.99      ( ~ v2_tex_2(X0,X1)
% 3.37/0.99      | m1_pre_topc(sK2(X1,X0),X1)
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | v1_xboole_0(X0)
% 3.37/0.99      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK3))
% 3.37/0.99      | sK4 != X0 ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2243,plain,
% 3.37/0.99      ( ~ v2_tex_2(sK4,X0)
% 3.37/0.99      | m1_pre_topc(sK2(X0,sK4),X0)
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | ~ v2_pre_topc(X0)
% 3.37/0.99      | ~ l1_pre_topc(X0)
% 3.37/0.99      | v1_xboole_0(sK4)
% 3.37/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_2242]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2247,plain,
% 3.37/0.99      ( ~ l1_pre_topc(X0)
% 3.37/0.99      | ~ v2_pre_topc(X0)
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | m1_pre_topc(sK2(X0,sK4),X0)
% 3.37/0.99      | ~ v2_tex_2(sK4,X0)
% 3.37/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_2243,c_29]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2248,plain,
% 3.37/0.99      ( ~ v2_tex_2(sK4,X0)
% 3.37/0.99      | m1_pre_topc(sK2(X0,sK4),X0)
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | ~ v2_pre_topc(X0)
% 3.37/0.99      | ~ l1_pre_topc(X0)
% 3.37/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_2247]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2249,plain,
% 3.37/0.99      ( k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK3))
% 3.37/0.99      | v2_tex_2(sK4,X0) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK2(X0,sK4),X0) = iProver_top
% 3.37/0.99      | v2_struct_0(X0) = iProver_top
% 3.37/0.99      | v2_pre_topc(X0) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_2248]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2251,plain,
% 3.37/0.99      ( k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
% 3.37/0.99      | v2_tex_2(sK4,sK3) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
% 3.37/0.99      | v2_struct_0(sK3) = iProver_top
% 3.37/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_2249]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4156,plain,( X0 = X0 ),theory(equality) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6924,plain,
% 3.37/0.99      ( k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(X0)) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_4156]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6929,plain,
% 3.37/0.99      ( k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_6924]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_7129,plain,
% 3.37/0.99      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_6763,c_34,c_35,c_37,c_2251,c_6929]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_12,plain,
% 3.37/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4995,plain,
% 3.37/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_7135,plain,
% 3.37/0.99      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK2(sK3,sK4)) = iProver_top
% 3.37/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_7129,c_4995]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_19,plain,
% 3.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v2_tdlat_3(X1)
% 3.37/0.99      | v2_tdlat_3(X0)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1305,plain,
% 3.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v2_tdlat_3(X2)
% 3.37/0.99      | ~ v2_tdlat_3(X1)
% 3.37/0.99      | v2_tdlat_3(X0)
% 3.37/0.99      | ~ l1_pre_topc(X2)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | X1 != X2 ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1306,plain,
% 3.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v2_tdlat_3(X1)
% 3.37/0.99      | v2_tdlat_3(X0)
% 3.37/0.99      | ~ l1_pre_topc(X1) ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_1305]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4977,plain,
% 3.37/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/0.99      | v2_struct_0(X1) = iProver_top
% 3.37/0.99      | v2_tdlat_3(X1) != iProver_top
% 3.37/0.99      | v2_tdlat_3(X0) = iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_1306]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_7136,plain,
% 3.37/0.99      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.37/0.99      | v2_struct_0(sK3) = iProver_top
% 3.37/0.99      | v2_tdlat_3(sK2(sK3,sK4)) = iProver_top
% 3.37/0.99      | v2_tdlat_3(sK3) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_7129,c_4977]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_31,negated_conjecture,
% 3.37/0.99      ( v2_tdlat_3(sK3) ),
% 3.37/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_36,plain,
% 3.37/0.99      ( v2_tdlat_3(sK3) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_7227,plain,
% 3.37/0.99      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.37/0.99      | v2_tdlat_3(sK2(sK3,sK4)) = iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_7136,c_34,c_36,c_37]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8768,plain,
% 3.37/0.99      ( v1_zfmisc_1(sK4) = iProver_top | k1_tarski(sK0(sK4)) = sK4 ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_8435,c_34,c_36,c_37,c_40,c_1066,c_1080,c_7135,c_7136]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8769,plain,
% 3.37/0.99      ( k1_tarski(sK0(sK4)) = sK4 | v1_zfmisc_1(sK4) = iProver_top ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_8768]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8774,plain,
% 3.37/0.99      ( k1_tarski(sK0(sK4)) = sK4 | v1_xboole_0(sK4) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_8769,c_8056]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8777,plain,
% 3.37/0.99      ( k1_tarski(sK0(sK4)) = sK4 ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_8434,c_38,c_8774]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_7,plain,
% 3.37/0.99      ( ~ r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4999,plain,
% 3.37/0.99      ( r1_tarski(k1_tarski(X0),X1) != iProver_top
% 3.37/0.99      | r2_hidden(X0,X1) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8793,plain,
% 3.37/0.99      ( r1_tarski(sK4,X0) != iProver_top
% 3.37/0.99      | r2_hidden(sK0(sK4),X0) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_8777,c_4999]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8,plain,
% 3.37/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4998,plain,
% 3.37/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.37/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_9098,plain,
% 3.37/0.99      ( m1_subset_1(sK0(sK4),X0) = iProver_top
% 3.37/0.99      | r1_tarski(sK4,X0) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_8793,c_4998]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_14,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,X1)
% 3.37/0.99      | v1_xboole_0(X1)
% 3.37/0.99      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4994,plain,
% 3.37/0.99      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 3.37/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.37/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_9306,plain,
% 3.37/0.99      ( k6_domain_1(X0,sK0(sK4)) = k1_tarski(sK0(sK4))
% 3.37/0.99      | r1_tarski(sK4,X0) != iProver_top
% 3.37/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_9098,c_4994]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_9310,plain,
% 3.37/0.99      ( k6_domain_1(X0,sK0(sK4)) = sK4
% 3.37/0.99      | r1_tarski(sK4,X0) != iProver_top
% 3.37/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.37/0.99      inference(light_normalisation,[status(thm)],[c_9306,c_8777]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5005,plain,
% 3.37/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.37/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_9097,plain,
% 3.37/0.99      ( r1_tarski(sK4,X0) != iProver_top
% 3.37/0.99      | v1_xboole_0(X0) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_8793,c_5005]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_10575,plain,
% 3.37/0.99      ( r1_tarski(sK4,X0) != iProver_top
% 3.37/0.99      | k6_domain_1(X0,sK0(sK4)) = sK4 ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_9310,c_9097]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_10576,plain,
% 3.37/0.99      ( k6_domain_1(X0,sK0(sK4)) = sK4
% 3.37/0.99      | r1_tarski(sK4,X0) != iProver_top ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_10575]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_10583,plain,
% 3.37/0.99      ( k6_domain_1(X0,sK0(sK4)) = sK4
% 3.37/0.99      | k1_tarski(sK1(sK4,X0)) = sK4
% 3.37/0.99      | v1_zfmisc_1(sK4) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_8057,c_10576]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_26,negated_conjecture,
% 3.37/0.99      ( ~ v2_tex_2(sK4,sK3) | ~ v1_zfmisc_1(sK4) ),
% 3.37/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_41,plain,
% 3.37/0.99      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.37/0.99      | v1_zfmisc_1(sK4) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_10,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4996,plain,
% 3.37/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.37/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5504,plain,
% 3.37/0.99      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_4984,c_4996]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5667,plain,
% 3.37/0.99      ( r2_hidden(sK0(sK4),sK4) | v1_xboole_0(sK4) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5668,plain,
% 3.37/0.99      ( r2_hidden(sK0(sK4),sK4) = iProver_top
% 3.37/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_5667]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4,plain,
% 3.37/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5835,plain,
% 3.37/0.99      ( ~ r1_tarski(sK4,X0)
% 3.37/0.99      | r2_hidden(sK0(sK4),X0)
% 3.37/0.99      | ~ r2_hidden(sK0(sK4),sK4) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6273,plain,
% 3.37/0.99      ( ~ r1_tarski(sK4,u1_struct_0(X0))
% 3.37/0.99      | r2_hidden(sK0(sK4),u1_struct_0(X0))
% 3.37/0.99      | ~ r2_hidden(sK0(sK4),sK4) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_5835]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6277,plain,
% 3.37/0.99      ( r1_tarski(sK4,u1_struct_0(X0)) != iProver_top
% 3.37/0.99      | r2_hidden(sK0(sK4),u1_struct_0(X0)) = iProver_top
% 3.37/0.99      | r2_hidden(sK0(sK4),sK4) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_6273]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6279,plain,
% 3.37/0.99      ( r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
% 3.37/0.99      | r2_hidden(sK0(sK4),u1_struct_0(sK3)) = iProver_top
% 3.37/0.99      | r2_hidden(sK0(sK4),sK4) != iProver_top ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_6277]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5274,plain,
% 3.37/0.99      ( m1_subset_1(X0,u1_struct_0(X1))
% 3.37/0.99      | ~ r2_hidden(X0,u1_struct_0(X1)) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8294,plain,
% 3.37/0.99      ( m1_subset_1(sK0(sK4),u1_struct_0(X0))
% 3.37/0.99      | ~ r2_hidden(sK0(sK4),u1_struct_0(X0)) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_5274]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8295,plain,
% 3.37/0.99      ( m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
% 3.37/0.99      | r2_hidden(sK0(sK4),u1_struct_0(X0)) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_8294]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8297,plain,
% 3.37/0.99      ( m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
% 3.37/0.99      | r2_hidden(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_8295]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5002,plain,
% 3.37/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.37/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.37/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5942,plain,
% 3.37/0.99      ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
% 3.37/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_5504,c_5002]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6094,plain,
% 3.37/0.99      ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
% 3.37/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_5942,c_4998]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6613,plain,
% 3.37/0.99      ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
% 3.37/0.99      | r2_hidden(X0,sK4) != iProver_top
% 3.37/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_6094,c_4994]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6093,plain,
% 3.37/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 3.37/0.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_5942,c_5005]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_7351,plain,
% 3.37/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 3.37/0.99      | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_6613,c_6093]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_7352,plain,
% 3.37/0.99      ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
% 3.37/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_7351]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_7359,plain,
% 3.37/0.99      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4))
% 3.37/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_5006,c_7352]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_7374,plain,
% 3.37/0.99      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_7359,c_38]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8781,plain,
% 3.37/0.99      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = sK4 ),
% 3.37/0.99      inference(demodulation,[status(thm)],[c_8777,c_7374]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_9627,plain,
% 3.37/0.99      ( v2_tex_2(sK4,sK3) = iProver_top
% 3.37/0.99      | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.37/0.99      | v2_struct_0(sK3) = iProver_top
% 3.37/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_8781,c_4987]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_12985,plain,
% 3.37/0.99      ( v1_zfmisc_1(sK4) != iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_10583,c_34,c_35,c_37,c_38,c_41,c_5504,c_5668,c_6279,
% 3.37/0.99                 c_8297,c_9627]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_12990,plain,
% 3.37/0.99      ( u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_6487,c_12985]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_13057,plain,
% 3.37/0.99      ( v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 3.37/0.99      | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 3.37/0.99      | v2_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 3.37/0.99      | v1_zfmisc_1(sK4) = iProver_top
% 3.37/0.99      | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_12990,c_4978]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4988,plain,
% 3.37/0.99      ( v2_tex_2(X0,X1) != iProver_top
% 3.37/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.37/0.99      | v2_struct_0(X1) = iProver_top
% 3.37/0.99      | v2_struct_0(sK2(X1,X0)) != iProver_top
% 3.37/0.99      | v2_pre_topc(X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top
% 3.37/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6649,plain,
% 3.37/0.99      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.37/0.99      | v2_struct_0(sK2(sK3,sK4)) != iProver_top
% 3.37/0.99      | v2_struct_0(sK3) = iProver_top
% 3.37/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.37/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_4984,c_4988]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2182,plain,
% 3.37/0.99      ( ~ v2_tex_2(X0,X1)
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v2_struct_0(sK2(X1,X0))
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | v1_xboole_0(X0)
% 3.37/0.99      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK3))
% 3.37/0.99      | sK4 != X0 ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2183,plain,
% 3.37/0.99      ( ~ v2_tex_2(sK4,X0)
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | ~ v2_struct_0(sK2(X0,sK4))
% 3.37/0.99      | ~ v2_pre_topc(X0)
% 3.37/0.99      | ~ l1_pre_topc(X0)
% 3.37/0.99      | v1_xboole_0(sK4)
% 3.37/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_2182]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2187,plain,
% 3.37/0.99      ( ~ l1_pre_topc(X0)
% 3.37/0.99      | ~ v2_pre_topc(X0)
% 3.37/0.99      | ~ v2_struct_0(sK2(X0,sK4))
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | ~ v2_tex_2(sK4,X0)
% 3.37/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_2183,c_29]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2188,plain,
% 3.37/0.99      ( ~ v2_tex_2(sK4,X0)
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | ~ v2_struct_0(sK2(X0,sK4))
% 3.37/0.99      | ~ v2_pre_topc(X0)
% 3.37/0.99      | ~ l1_pre_topc(X0)
% 3.37/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_2187]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2189,plain,
% 3.37/0.99      ( k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK3))
% 3.37/0.99      | v2_tex_2(sK4,X0) != iProver_top
% 3.37/0.99      | v2_struct_0(X0) = iProver_top
% 3.37/0.99      | v2_struct_0(sK2(X0,sK4)) != iProver_top
% 3.37/0.99      | v2_pre_topc(X0) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_2188]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2191,plain,
% 3.37/0.99      ( k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
% 3.37/0.99      | v2_tex_2(sK4,sK3) != iProver_top
% 3.37/0.99      | v2_struct_0(sK2(sK3,sK4)) != iProver_top
% 3.37/0.99      | v2_struct_0(sK3) = iProver_top
% 3.37/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_2189]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_7122,plain,
% 3.37/0.99      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.37/0.99      | v2_struct_0(sK2(sK3,sK4)) != iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_6649,c_34,c_35,c_37,c_2191,c_6929]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4989,plain,
% 3.37/0.99      ( v2_tex_2(X0,X1) != iProver_top
% 3.37/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.37/0.99      | v2_struct_0(X1) = iProver_top
% 3.37/0.99      | v1_tdlat_3(sK2(X1,X0)) = iProver_top
% 3.37/0.99      | v2_pre_topc(X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top
% 3.37/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6359,plain,
% 3.37/0.99      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.37/0.99      | v2_struct_0(sK3) = iProver_top
% 3.37/0.99      | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
% 3.37/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.37/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_4984,c_4989]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6474,plain,
% 3.37/0.99      ( v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
% 3.37/0.99      | v2_tex_2(sK4,sK3) != iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_6359,c_34,c_35,c_37,c_38]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6475,plain,
% 3.37/0.99      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.37/0.99      | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_6474]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(contradiction,plain,
% 3.37/0.99      ( $false ),
% 3.37/0.99      inference(minisat,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_13057,c_9627,c_8297,c_7227,c_7135,c_7122,c_6475,
% 3.37/0.99                 c_6279,c_5668,c_5504,c_41,c_38,c_37,c_35,c_34]) ).
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.37/0.99  
% 3.37/0.99  ------                               Statistics
% 3.37/0.99  
% 3.37/0.99  ------ General
% 3.37/0.99  
% 3.37/0.99  abstr_ref_over_cycles:                  0
% 3.37/0.99  abstr_ref_under_cycles:                 0
% 3.37/0.99  gc_basic_clause_elim:                   0
% 3.37/0.99  forced_gc_time:                         0
% 3.37/0.99  parsing_time:                           0.022
% 3.37/0.99  unif_index_cands_time:                  0.
% 3.37/0.99  unif_index_add_time:                    0.
% 3.37/0.99  orderings_time:                         0.
% 3.37/0.99  out_proof_time:                         0.011
% 3.37/0.99  total_time:                             0.385
% 3.37/0.99  num_of_symbols:                         54
% 3.37/0.99  num_of_terms:                           6757
% 3.37/0.99  
% 3.37/0.99  ------ Preprocessing
% 3.37/0.99  
% 3.37/0.99  num_of_splits:                          0
% 3.37/0.99  num_of_split_atoms:                     0
% 3.37/0.99  num_of_reused_defs:                     0
% 3.37/0.99  num_eq_ax_congr_red:                    32
% 3.37/0.99  num_of_sem_filtered_clauses:            1
% 3.37/0.99  num_of_subtypes:                        0
% 3.37/0.99  monotx_restored_types:                  0
% 3.37/0.99  sat_num_of_epr_types:                   0
% 3.37/0.99  sat_num_of_non_cyclic_types:            0
% 3.37/0.99  sat_guarded_non_collapsed_types:        0
% 3.37/0.99  num_pure_diseq_elim:                    0
% 3.37/0.99  simp_replaced_by:                       0
% 3.37/0.99  res_preprocessed:                       157
% 3.37/0.99  prep_upred:                             0
% 3.37/0.99  prep_unflattend:                        159
% 3.37/0.99  smt_new_axioms:                         0
% 3.37/0.99  pred_elim_cands:                        12
% 3.37/0.99  pred_elim:                              2
% 3.37/0.99  pred_elim_cl:                           2
% 3.37/0.99  pred_elim_cycles:                       18
% 3.37/0.99  merged_defs:                            24
% 3.37/0.99  merged_defs_ncl:                        0
% 3.37/0.99  bin_hyper_res:                          24
% 3.37/0.99  prep_cycles:                            4
% 3.37/0.99  pred_elim_time:                         0.126
% 3.37/0.99  splitting_time:                         0.
% 3.37/0.99  sem_filter_time:                        0.
% 3.37/0.99  monotx_time:                            0.
% 3.37/0.99  subtype_inf_time:                       0.
% 3.37/0.99  
% 3.37/0.99  ------ Problem properties
% 3.37/0.99  
% 3.37/0.99  clauses:                                30
% 3.37/0.99  conjectures:                            8
% 3.37/0.99  epr:                                    14
% 3.37/0.99  horn:                                   18
% 3.37/0.99  ground:                                 8
% 3.37/0.99  unary:                                  7
% 3.37/0.99  binary:                                 11
% 3.37/0.99  lits:                                   89
% 3.37/0.99  lits_eq:                                3
% 3.37/0.99  fd_pure:                                0
% 3.37/0.99  fd_pseudo:                              0
% 3.37/0.99  fd_cond:                                0
% 3.37/0.99  fd_pseudo_cond:                         1
% 3.37/0.99  ac_symbols:                             0
% 3.37/0.99  
% 3.37/0.99  ------ Propositional Solver
% 3.37/0.99  
% 3.37/0.99  prop_solver_calls:                      31
% 3.37/0.99  prop_fast_solver_calls:                 2258
% 3.37/0.99  smt_solver_calls:                       0
% 3.37/0.99  smt_fast_solver_calls:                  0
% 3.37/0.99  prop_num_of_clauses:                    3475
% 3.37/0.99  prop_preprocess_simplified:             9008
% 3.37/0.99  prop_fo_subsumed:                       159
% 3.37/0.99  prop_solver_time:                       0.
% 3.37/0.99  smt_solver_time:                        0.
% 3.37/0.99  smt_fast_solver_time:                   0.
% 3.37/0.99  prop_fast_solver_time:                  0.
% 3.37/0.99  prop_unsat_core_time:                   0.
% 3.37/0.99  
% 3.37/0.99  ------ QBF
% 3.37/0.99  
% 3.37/0.99  qbf_q_res:                              0
% 3.37/0.99  qbf_num_tautologies:                    0
% 3.37/0.99  qbf_prep_cycles:                        0
% 3.37/0.99  
% 3.37/0.99  ------ BMC1
% 3.37/0.99  
% 3.37/0.99  bmc1_current_bound:                     -1
% 3.37/0.99  bmc1_last_solved_bound:                 -1
% 3.37/0.99  bmc1_unsat_core_size:                   -1
% 3.37/0.99  bmc1_unsat_core_parents_size:           -1
% 3.37/0.99  bmc1_merge_next_fun:                    0
% 3.37/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.37/0.99  
% 3.37/0.99  ------ Instantiation
% 3.37/0.99  
% 3.37/0.99  inst_num_of_clauses:                    753
% 3.37/0.99  inst_num_in_passive:                    253
% 3.37/0.99  inst_num_in_active:                     381
% 3.37/0.99  inst_num_in_unprocessed:                119
% 3.37/0.99  inst_num_of_loops:                      610
% 3.37/0.99  inst_num_of_learning_restarts:          0
% 3.37/0.99  inst_num_moves_active_passive:          222
% 3.37/0.99  inst_lit_activity:                      0
% 3.37/0.99  inst_lit_activity_moves:                0
% 3.37/0.99  inst_num_tautologies:                   0
% 3.37/0.99  inst_num_prop_implied:                  0
% 3.37/0.99  inst_num_existing_simplified:           0
% 3.37/0.99  inst_num_eq_res_simplified:             0
% 3.37/0.99  inst_num_child_elim:                    0
% 3.37/0.99  inst_num_of_dismatching_blockings:      305
% 3.37/0.99  inst_num_of_non_proper_insts:           996
% 3.37/0.99  inst_num_of_duplicates:                 0
% 3.37/0.99  inst_inst_num_from_inst_to_res:         0
% 3.37/0.99  inst_dismatching_checking_time:         0.
% 3.37/0.99  
% 3.37/0.99  ------ Resolution
% 3.37/0.99  
% 3.37/0.99  res_num_of_clauses:                     0
% 3.37/0.99  res_num_in_passive:                     0
% 3.37/0.99  res_num_in_active:                      0
% 3.37/0.99  res_num_of_loops:                       161
% 3.37/0.99  res_forward_subset_subsumed:            92
% 3.37/0.99  res_backward_subset_subsumed:           0
% 3.37/0.99  res_forward_subsumed:                   0
% 3.37/0.99  res_backward_subsumed:                  1
% 3.37/0.99  res_forward_subsumption_resolution:     2
% 3.37/0.99  res_backward_subsumption_resolution:    0
% 3.37/0.99  res_clause_to_clause_subsumption:       668
% 3.37/0.99  res_orphan_elimination:                 0
% 3.37/0.99  res_tautology_del:                      135
% 3.37/0.99  res_num_eq_res_simplified:              0
% 3.37/0.99  res_num_sel_changes:                    0
% 3.37/0.99  res_moves_from_active_to_pass:          0
% 3.37/0.99  
% 3.37/0.99  ------ Superposition
% 3.37/0.99  
% 3.37/0.99  sup_time_total:                         0.
% 3.37/0.99  sup_time_generating:                    0.
% 3.37/0.99  sup_time_sim_full:                      0.
% 3.37/0.99  sup_time_sim_immed:                     0.
% 3.37/0.99  
% 3.37/0.99  sup_num_of_clauses:                     236
% 3.37/0.99  sup_num_in_active:                      112
% 3.37/0.99  sup_num_in_passive:                     124
% 3.37/0.99  sup_num_of_loops:                       120
% 3.37/0.99  sup_fw_superposition:                   137
% 3.37/0.99  sup_bw_superposition:                   205
% 3.37/0.99  sup_immediate_simplified:               69
% 3.37/0.99  sup_given_eliminated:                   0
% 3.37/0.99  comparisons_done:                       0
% 3.37/0.99  comparisons_avoided:                    17
% 3.37/0.99  
% 3.37/0.99  ------ Simplifications
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  sim_fw_subset_subsumed:                 21
% 3.37/0.99  sim_bw_subset_subsumed:                 15
% 3.37/0.99  sim_fw_subsumed:                        22
% 3.37/0.99  sim_bw_subsumed:                        1
% 3.37/0.99  sim_fw_subsumption_res:                 0
% 3.37/0.99  sim_bw_subsumption_res:                 0
% 3.37/0.99  sim_tautology_del:                      13
% 3.37/0.99  sim_eq_tautology_del:                   11
% 3.37/0.99  sim_eq_res_simp:                        0
% 3.37/0.99  sim_fw_demodulated:                     3
% 3.37/0.99  sim_bw_demodulated:                     2
% 3.37/0.99  sim_light_normalised:                   34
% 3.37/0.99  sim_joinable_taut:                      0
% 3.37/0.99  sim_joinable_simp:                      0
% 3.37/0.99  sim_ac_normalised:                      0
% 3.37/0.99  sim_smt_subsumption:                    0
% 3.37/0.99  
%------------------------------------------------------------------------------
