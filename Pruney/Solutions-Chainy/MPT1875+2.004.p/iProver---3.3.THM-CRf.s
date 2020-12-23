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
% DateTime   : Thu Dec  3 12:26:41 EST 2020

% Result     : Theorem 4.18s
% Output     : CNFRefutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :  204 (1245 expanded)
%              Number of clauses        :  119 ( 376 expanded)
%              Number of leaves         :   25 ( 297 expanded)
%              Depth                    :   20
%              Number of atoms          :  737 (5819 expanded)
%              Number of equality atoms :  284 ( 770 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
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

fof(f56,plain,
    ( ~ v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v1_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f39,f55,f54])).

fof(f88,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f56])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK1(X0,X1)) = X1
        & m1_pre_topc(sK1(X0,X1),X0)
        & ~ v2_struct_0(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK1(X0,X1)) = X1
            & m1_pre_topc(sK1(X0,X1),X0)
            & ~ v2_struct_0(sK1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f47])).

fof(f77,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f84,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
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
    inference(nnf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f89,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v1_tdlat_3(X1) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f73,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1278,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1286,plain,
    ( u1_struct_0(sK1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3228,plain,
    ( u1_struct_0(sK1(sK3,sK4)) = sK4
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1278,c_1286])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_33,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3657,plain,
    ( u1_struct_0(sK1(sK3,sK4)) = sK4
    | v1_xboole_0(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3228,c_33,c_36])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1294,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1297,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_203,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_204,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_203])).

cnf(c_264,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_14,c_204])).

cnf(c_1271,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_264])).

cnf(c_2932,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1297,c_1271])).

cnf(c_3032,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1294,c_2932])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1293,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4135,plain,
    ( k3_xboole_0(X0,X1) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3032,c_1293])).

cnf(c_4385,plain,
    ( k3_xboole_0(sK4,X0) = sK4
    | u1_struct_0(sK1(sK3,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_3657,c_4135])).

cnf(c_10,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1292,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1315,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1292,c_9])).

cnf(c_3229,plain,
    ( u1_struct_0(sK1(X0,u1_struct_0(X0))) = u1_struct_0(X0)
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_1286])).

cnf(c_7717,plain,
    ( k3_xboole_0(sK4,X0) = sK4
    | u1_struct_0(sK1(sK1(sK3,sK4),u1_struct_0(sK1(sK3,sK4)))) = u1_struct_0(sK1(sK3,sK4))
    | v2_struct_0(sK1(sK3,sK4)) = iProver_top
    | l1_pre_topc(sK1(sK3,sK4)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4385,c_3229])).

cnf(c_27,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_38,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_92,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_96,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_562,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2378,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_562])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1284,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK1(X1,X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3349,plain,
    ( v2_struct_0(sK1(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1278,c_1284])).

cnf(c_3664,plain,
    ( v2_struct_0(sK1(sK3,sK4)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3349,c_33,c_36])).

cnf(c_19,plain,
    ( m1_pre_topc(sK1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1285,plain,
    ( m1_pre_topc(sK1(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3405,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1278,c_1285])).

cnf(c_3845,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3405,c_33,c_36])).

cnf(c_563,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2381,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_2992,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2381])).

cnf(c_5737,plain,
    ( u1_struct_0(sK1(sK3,sK4)) != sK4
    | sK4 = u1_struct_0(sK1(sK3,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2992])).

cnf(c_21,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_331,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_tex_2(u1_struct_0(X0),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_15])).

cnf(c_332,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_331])).

cnf(c_5801,plain,
    ( v2_tex_2(u1_struct_0(sK1(sK3,sK4)),sK3)
    | ~ m1_pre_topc(sK1(sK3,sK4),sK3)
    | v2_struct_0(sK1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ v1_tdlat_3(sK1(sK3,sK4))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_5805,plain,
    ( v2_tex_2(u1_struct_0(sK1(sK3,sK4)),sK3) = iProver_top
    | m1_pre_topc(sK1(sK3,sK4),sK3) != iProver_top
    | v2_struct_0(sK1(sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_tdlat_3(sK1(sK3,sK4)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5801])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | v1_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1287,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_tdlat_3(X1) != iProver_top
    | v1_tdlat_3(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1288,plain,
    ( v1_tdlat_3(X0) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1414,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_tdlat_3(X1) != iProver_top
    | v1_tdlat_3(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1287,c_1288])).

cnf(c_6201,plain,
    ( v2_struct_0(sK3) = iProver_top
    | v1_tdlat_3(sK1(sK3,sK4)) = iProver_top
    | v1_tdlat_3(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3845,c_1414])).

cnf(c_30,negated_conjecture,
    ( v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_35,plain,
    ( v1_tdlat_3(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7013,plain,
    ( v1_tdlat_3(sK1(sK3,sK4)) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6201,c_33,c_35,c_36])).

cnf(c_575,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2201,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK4,sK3)
    | sK3 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_575])).

cnf(c_11082,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1(sK3,sK4)),X0)
    | v2_tex_2(sK4,sK3)
    | sK3 != X0
    | sK4 != u1_struct_0(sK1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2201])).

cnf(c_11083,plain,
    ( sK3 != X0
    | sK4 != u1_struct_0(sK1(sK3,sK4))
    | v2_tex_2(u1_struct_0(sK1(sK3,sK4)),X0) != iProver_top
    | v2_tex_2(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11082])).

cnf(c_11085,plain,
    ( sK3 != sK3
    | sK4 != u1_struct_0(sK1(sK3,sK4))
    | v2_tex_2(u1_struct_0(sK1(sK3,sK4)),sK3) != iProver_top
    | v2_tex_2(sK4,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_11083])).

cnf(c_11490,plain,
    ( v1_xboole_0(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7717,c_33,c_36,c_38,c_92,c_96,c_2378,c_3657,c_3664,c_3845,c_5737,c_5805,c_7013,c_11085])).

cnf(c_11495,plain,
    ( k3_xboole_0(sK4,X0) = sK4 ),
    inference(superposition,[status(thm)],[c_11490,c_4135])).

cnf(c_14692,plain,
    ( k3_xboole_0(X0,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_0,c_11495])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1290,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1924,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1278,c_1290])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_260,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_204])).

cnf(c_1273,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_260])).

cnf(c_2713,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,X0) = k9_subset_1(u1_struct_0(sK3),X0,sK4) ),
    inference(superposition,[status(thm)],[c_1924,c_1273])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_261,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_204])).

cnf(c_1272,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_2210,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK4) = k3_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_1924,c_1272])).

cnf(c_2715,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,X0) = k3_xboole_0(X0,sK4) ),
    inference(light_normalisation,[status(thm)],[c_2713,c_2210])).

cnf(c_15051,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,X0) = sK4 ),
    inference(demodulation,[status(thm)],[c_14692,c_2715])).

cnf(c_23,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,sK2(X1,X0))) != sK2(X1,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1283,plain,
    ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
    | v2_tex_2(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_15213,plain,
    ( sK2(sK3,sK4) != sK4
    | v2_tex_2(sK4,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_15051,c_1283])).

cnf(c_1289,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3192,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1289,c_1290])).

cnf(c_6745,plain,
    ( k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X0)
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3192,c_1293])).

cnf(c_7585,plain,
    ( k3_xboole_0(u1_struct_0(sK1(sK3,sK4)),u1_struct_0(sK3)) = u1_struct_0(sK1(sK3,sK4))
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3845,c_6745])).

cnf(c_7981,plain,
    ( k3_xboole_0(u1_struct_0(sK1(sK3,sK4)),u1_struct_0(sK3)) = u1_struct_0(sK1(sK3,sK4))
    | v1_xboole_0(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7585,c_36])).

cnf(c_24,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1282,plain,
    ( v2_tex_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(sK2(X1,X0),X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5108,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | r1_tarski(sK2(sK3,sK4),sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1278,c_1282])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_34,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1655,plain,
    ( v2_tex_2(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK2(sK3,sK4),sK4)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1656,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK2(sK3,sK4),sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1655])).

cnf(c_5486,plain,
    ( r1_tarski(sK2(sK3,sK4),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5108,c_33,c_34,c_36,c_37,c_38,c_1656])).

cnf(c_1295,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4134,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3032,c_1295])).

cnf(c_5491,plain,
    ( sK2(sK3,sK4) = sK4
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5486,c_4134])).

cnf(c_7992,plain,
    ( sK2(sK3,sK4) = sK4
    | k3_xboole_0(u1_struct_0(sK1(sK3,sK4)),u1_struct_0(sK3)) = u1_struct_0(sK1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_7981,c_5491])).

cnf(c_5494,plain,
    ( k3_xboole_0(sK2(sK3,sK4),sK4) = sK2(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_5486,c_1293])).

cnf(c_4399,plain,
    ( k3_xboole_0(X0,sK4) = sK4
    | u1_struct_0(sK1(sK3,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_4385,c_0])).

cnf(c_5750,plain,
    ( sK2(sK3,sK4) = sK4
    | u1_struct_0(sK1(sK3,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_5494,c_4399])).

cnf(c_1269,plain,
    ( v2_tex_2(u1_struct_0(X0),X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_6301,plain,
    ( sK2(sK3,sK4) = sK4
    | v2_tex_2(sK4,X0) = iProver_top
    | m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1(sK3,sK4)) = iProver_top
    | v1_tdlat_3(sK1(sK3,sK4)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5750,c_1269])).

cnf(c_6469,plain,
    ( sK2(sK3,sK4) = sK4
    | v2_tex_2(sK4,sK3) = iProver_top
    | m1_pre_topc(sK1(sK3,sK4),sK3) != iProver_top
    | v2_struct_0(sK1(sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_tdlat_3(sK1(sK3,sK4)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6301])).

cnf(c_8214,plain,
    ( sK2(sK3,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7992,c_33,c_36,c_38,c_3664,c_3845,c_5491,c_6469,c_7013])).

cnf(c_15221,plain,
    ( sK4 != sK4
    | v2_tex_2(sK4,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15213,c_8214])).

cnf(c_15222,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15221])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15222,c_38,c_37,c_36,c_34,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.33  % CPULimit   : 60
% 0.19/0.33  % WCLimit    : 600
% 0.19/0.33  % DateTime   : Tue Dec  1 20:24:42 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 4.18/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.18/1.01  
% 4.18/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.18/1.01  
% 4.18/1.01  ------  iProver source info
% 4.18/1.01  
% 4.18/1.01  git: date: 2020-06-30 10:37:57 +0100
% 4.18/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.18/1.01  git: non_committed_changes: false
% 4.18/1.01  git: last_make_outside_of_git: false
% 4.18/1.01  
% 4.18/1.01  ------ 
% 4.18/1.01  ------ Parsing...
% 4.18/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.18/1.01  
% 4.18/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 4.18/1.01  
% 4.18/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.18/1.01  
% 4.18/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.18/1.01  ------ Proving...
% 4.18/1.01  ------ Problem Properties 
% 4.18/1.01  
% 4.18/1.01  
% 4.18/1.01  clauses                                 32
% 4.18/1.01  conjectures                             6
% 4.18/1.01  EPR                                     11
% 4.18/1.01  Horn                                    21
% 4.18/1.01  unary                                   10
% 4.18/1.01  binary                                  7
% 4.18/1.01  lits                                    98
% 4.18/1.01  lits eq                                 9
% 4.18/1.01  fd_pure                                 0
% 4.18/1.01  fd_pseudo                               0
% 4.18/1.01  fd_cond                                 0
% 4.18/1.01  fd_pseudo_cond                          1
% 4.18/1.01  AC symbols                              0
% 4.18/1.01  
% 4.18/1.01  ------ Input Options Time Limit: Unbounded
% 4.18/1.01  
% 4.18/1.01  
% 4.18/1.01  ------ 
% 4.18/1.01  Current options:
% 4.18/1.01  ------ 
% 4.18/1.01  
% 4.18/1.01  
% 4.18/1.01  
% 4.18/1.01  
% 4.18/1.01  ------ Proving...
% 4.18/1.01  
% 4.18/1.01  
% 4.18/1.01  % SZS status Theorem for theBenchmark.p
% 4.18/1.01  
% 4.18/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 4.18/1.01  
% 4.18/1.01  fof(f1,axiom,(
% 4.18/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.01  
% 4.18/1.01  fof(f57,plain,(
% 4.18/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.18/1.01    inference(cnf_transformation,[],[f1])).
% 4.18/1.01  
% 4.18/1.01  fof(f17,conjecture,(
% 4.18/1.01    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 4.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.01  
% 4.18/1.01  fof(f18,negated_conjecture,(
% 4.18/1.01    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 4.18/1.01    inference(negated_conjecture,[],[f17])).
% 4.18/1.01  
% 4.18/1.01  fof(f38,plain,(
% 4.18/1.01    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 4.18/1.01    inference(ennf_transformation,[],[f18])).
% 4.18/1.01  
% 4.18/1.01  fof(f39,plain,(
% 4.18/1.01    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.18/1.01    inference(flattening,[],[f38])).
% 4.18/1.01  
% 4.18/1.01  fof(f55,plain,(
% 4.18/1.01    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.18/1.01    introduced(choice_axiom,[])).
% 4.18/1.01  
% 4.18/1.01  fof(f54,plain,(
% 4.18/1.01    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v1_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 4.18/1.01    introduced(choice_axiom,[])).
% 4.18/1.01  
% 4.18/1.01  fof(f56,plain,(
% 4.18/1.01    (~v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v1_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 4.18/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f39,f55,f54])).
% 4.18/1.01  
% 4.18/1.01  fof(f88,plain,(
% 4.18/1.01    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 4.18/1.01    inference(cnf_transformation,[],[f56])).
% 4.18/1.01  
% 4.18/1.01  fof(f14,axiom,(
% 4.18/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 4.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.01  
% 4.18/1.01  fof(f19,plain,(
% 4.18/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 4.18/1.01    inference(pure_predicate_removal,[],[f14])).
% 4.18/1.01  
% 4.18/1.01  fof(f32,plain,(
% 4.18/1.01    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 4.18/1.01    inference(ennf_transformation,[],[f19])).
% 4.18/1.01  
% 4.18/1.01  fof(f33,plain,(
% 4.18/1.01    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 4.18/1.01    inference(flattening,[],[f32])).
% 4.18/1.01  
% 4.18/1.01  fof(f47,plain,(
% 4.18/1.01    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & ~v2_struct_0(sK1(X0,X1))))),
% 4.18/1.01    introduced(choice_axiom,[])).
% 4.18/1.01  
% 4.18/1.01  fof(f48,plain,(
% 4.18/1.01    ! [X0] : (! [X1] : ((u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & ~v2_struct_0(sK1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 4.18/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f47])).
% 4.18/1.01  
% 4.18/1.01  fof(f77,plain,(
% 4.18/1.01    ( ! [X0,X1] : (u1_struct_0(sK1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.18/1.01    inference(cnf_transformation,[],[f48])).
% 4.18/1.01  
% 4.18/1.01  fof(f84,plain,(
% 4.18/1.01    ~v2_struct_0(sK3)),
% 4.18/1.01    inference(cnf_transformation,[],[f56])).
% 4.18/1.01  
% 4.18/1.01  fof(f87,plain,(
% 4.18/1.01    l1_pre_topc(sK3)),
% 4.18/1.01    inference(cnf_transformation,[],[f56])).
% 4.18/1.01  
% 4.18/1.01  fof(f3,axiom,(
% 4.18/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.01  
% 4.18/1.01  fof(f44,plain,(
% 4.18/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.18/1.01    inference(nnf_transformation,[],[f3])).
% 4.18/1.01  
% 4.18/1.01  fof(f45,plain,(
% 4.18/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.18/1.01    inference(flattening,[],[f44])).
% 4.18/1.01  
% 4.18/1.01  fof(f61,plain,(
% 4.18/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.18/1.01    inference(cnf_transformation,[],[f45])).
% 4.18/1.01  
% 4.18/1.01  fof(f91,plain,(
% 4.18/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.18/1.01    inference(equality_resolution,[],[f61])).
% 4.18/1.01  
% 4.18/1.01  fof(f2,axiom,(
% 4.18/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.01  
% 4.18/1.01  fof(f22,plain,(
% 4.18/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.18/1.01    inference(ennf_transformation,[],[f2])).
% 4.18/1.01  
% 4.18/1.01  fof(f40,plain,(
% 4.18/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 4.18/1.01    inference(nnf_transformation,[],[f22])).
% 4.18/1.01  
% 4.18/1.01  fof(f41,plain,(
% 4.18/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.18/1.01    inference(rectify,[],[f40])).
% 4.18/1.01  
% 4.18/1.01  fof(f42,plain,(
% 4.18/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 4.18/1.01    introduced(choice_axiom,[])).
% 4.18/1.01  
% 4.18/1.01  fof(f43,plain,(
% 4.18/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.18/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 4.18/1.01  
% 4.18/1.01  fof(f59,plain,(
% 4.18/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 4.18/1.01    inference(cnf_transformation,[],[f43])).
% 4.18/1.01  
% 4.18/1.01  fof(f10,axiom,(
% 4.18/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 4.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.01  
% 4.18/1.01  fof(f26,plain,(
% 4.18/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 4.18/1.01    inference(ennf_transformation,[],[f10])).
% 4.18/1.01  
% 4.18/1.01  fof(f71,plain,(
% 4.18/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 4.18/1.01    inference(cnf_transformation,[],[f26])).
% 4.18/1.01  
% 4.18/1.01  fof(f9,axiom,(
% 4.18/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.01  
% 4.18/1.01  fof(f46,plain,(
% 4.18/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.18/1.01    inference(nnf_transformation,[],[f9])).
% 4.18/1.01  
% 4.18/1.01  fof(f70,plain,(
% 4.18/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.18/1.01    inference(cnf_transformation,[],[f46])).
% 4.18/1.01  
% 4.18/1.01  fof(f4,axiom,(
% 4.18/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.01  
% 4.18/1.01  fof(f23,plain,(
% 4.18/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.18/1.01    inference(ennf_transformation,[],[f4])).
% 4.18/1.01  
% 4.18/1.01  fof(f64,plain,(
% 4.18/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 4.18/1.01    inference(cnf_transformation,[],[f23])).
% 4.18/1.01  
% 4.18/1.01  fof(f7,axiom,(
% 4.18/1.01    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 4.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.01  
% 4.18/1.01  fof(f67,plain,(
% 4.18/1.01    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 4.18/1.01    inference(cnf_transformation,[],[f7])).
% 4.18/1.01  
% 4.18/1.01  fof(f6,axiom,(
% 4.18/1.01    ! [X0] : k2_subset_1(X0) = X0),
% 4.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.01  
% 4.18/1.01  fof(f66,plain,(
% 4.18/1.01    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 4.18/1.01    inference(cnf_transformation,[],[f6])).
% 4.18/1.01  
% 4.18/1.01  fof(f89,plain,(
% 4.18/1.01    ~v2_tex_2(sK4,sK3)),
% 4.18/1.01    inference(cnf_transformation,[],[f56])).
% 4.18/1.01  
% 4.18/1.01  fof(f63,plain,(
% 4.18/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.18/1.01    inference(cnf_transformation,[],[f45])).
% 4.18/1.01  
% 4.18/1.01  fof(f75,plain,(
% 4.18/1.01    ( ! [X0,X1] : (~v2_struct_0(sK1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.18/1.01    inference(cnf_transformation,[],[f48])).
% 4.18/1.01  
% 4.18/1.01  fof(f76,plain,(
% 4.18/1.01    ( ! [X0,X1] : (m1_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.18/1.01    inference(cnf_transformation,[],[f48])).
% 4.18/1.01  
% 4.18/1.01  fof(f15,axiom,(
% 4.18/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 4.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.01  
% 4.18/1.01  fof(f34,plain,(
% 4.18/1.01    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 4.18/1.01    inference(ennf_transformation,[],[f15])).
% 4.18/1.01  
% 4.18/1.01  fof(f35,plain,(
% 4.18/1.01    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 4.18/1.01    inference(flattening,[],[f34])).
% 4.18/1.01  
% 4.18/1.01  fof(f49,plain,(
% 4.18/1.01    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 4.18/1.01    inference(nnf_transformation,[],[f35])).
% 4.18/1.01  
% 4.18/1.01  fof(f79,plain,(
% 4.18/1.01    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.18/1.01    inference(cnf_transformation,[],[f49])).
% 4.18/1.01  
% 4.18/1.01  fof(f92,plain,(
% 4.18/1.01    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.18/1.01    inference(equality_resolution,[],[f79])).
% 4.18/1.01  
% 4.18/1.01  fof(f11,axiom,(
% 4.18/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.01  
% 4.18/1.01  fof(f27,plain,(
% 4.18/1.01    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.18/1.01    inference(ennf_transformation,[],[f11])).
% 4.18/1.01  
% 4.18/1.01  fof(f72,plain,(
% 4.18/1.01    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.18/1.01    inference(cnf_transformation,[],[f27])).
% 4.18/1.01  
% 4.18/1.01  fof(f13,axiom,(
% 4.18/1.01    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 4.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.01  
% 4.18/1.01  fof(f20,plain,(
% 4.18/1.01    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 4.18/1.01    inference(pure_predicate_removal,[],[f13])).
% 4.18/1.01  
% 4.18/1.01  fof(f21,plain,(
% 4.18/1.01    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v1_tdlat_3(X1)))),
% 4.18/1.01    inference(pure_predicate_removal,[],[f20])).
% 4.18/1.01  
% 4.18/1.01  fof(f30,plain,(
% 4.18/1.01    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.18/1.01    inference(ennf_transformation,[],[f21])).
% 4.18/1.01  
% 4.18/1.01  fof(f31,plain,(
% 4.18/1.01    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.18/1.01    inference(flattening,[],[f30])).
% 4.18/1.01  
% 4.18/1.01  fof(f74,plain,(
% 4.18/1.01    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.18/1.01    inference(cnf_transformation,[],[f31])).
% 4.18/1.01  
% 4.18/1.01  fof(f12,axiom,(
% 4.18/1.01    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 4.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.01  
% 4.18/1.01  fof(f28,plain,(
% 4.18/1.01    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 4.18/1.01    inference(ennf_transformation,[],[f12])).
% 4.18/1.01  
% 4.18/1.01  fof(f29,plain,(
% 4.18/1.01    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 4.18/1.01    inference(flattening,[],[f28])).
% 4.18/1.01  
% 4.18/1.01  fof(f73,plain,(
% 4.18/1.01    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 4.18/1.01    inference(cnf_transformation,[],[f29])).
% 4.18/1.01  
% 4.18/1.01  fof(f86,plain,(
% 4.18/1.01    v1_tdlat_3(sK3)),
% 4.18/1.01    inference(cnf_transformation,[],[f56])).
% 4.18/1.01  
% 4.18/1.01  fof(f69,plain,(
% 4.18/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.18/1.01    inference(cnf_transformation,[],[f46])).
% 4.18/1.01  
% 4.18/1.01  fof(f5,axiom,(
% 4.18/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 4.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.01  
% 4.18/1.01  fof(f24,plain,(
% 4.18/1.01    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.18/1.01    inference(ennf_transformation,[],[f5])).
% 4.18/1.01  
% 4.18/1.01  fof(f65,plain,(
% 4.18/1.01    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.18/1.01    inference(cnf_transformation,[],[f24])).
% 4.18/1.01  
% 4.18/1.01  fof(f8,axiom,(
% 4.18/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 4.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.01  
% 4.18/1.01  fof(f25,plain,(
% 4.18/1.01    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.18/1.01    inference(ennf_transformation,[],[f8])).
% 4.18/1.01  
% 4.18/1.01  fof(f68,plain,(
% 4.18/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.18/1.01    inference(cnf_transformation,[],[f25])).
% 4.18/1.01  
% 4.18/1.01  fof(f16,axiom,(
% 4.18/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 4.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.01  
% 4.18/1.01  fof(f36,plain,(
% 4.18/1.01    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.18/1.01    inference(ennf_transformation,[],[f16])).
% 4.18/1.01  
% 4.18/1.01  fof(f37,plain,(
% 4.18/1.01    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.18/1.01    inference(flattening,[],[f36])).
% 4.18/1.01  
% 4.18/1.01  fof(f50,plain,(
% 4.18/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.18/1.01    inference(nnf_transformation,[],[f37])).
% 4.18/1.01  
% 4.18/1.01  fof(f51,plain,(
% 4.18/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.18/1.01    inference(rectify,[],[f50])).
% 4.18/1.01  
% 4.18/1.01  fof(f52,plain,(
% 4.18/1.01    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.18/1.01    introduced(choice_axiom,[])).
% 4.18/1.01  
% 4.18/1.01  fof(f53,plain,(
% 4.18/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.18/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).
% 4.18/1.01  
% 4.18/1.01  fof(f83,plain,(
% 4.18/1.01    ( ! [X0,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.18/1.01    inference(cnf_transformation,[],[f53])).
% 4.18/1.01  
% 4.18/1.01  fof(f82,plain,(
% 4.18/1.01    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.18/1.01    inference(cnf_transformation,[],[f53])).
% 4.18/1.01  
% 4.18/1.01  fof(f85,plain,(
% 4.18/1.01    v2_pre_topc(sK3)),
% 4.18/1.01    inference(cnf_transformation,[],[f56])).
% 4.18/1.01  
% 4.18/1.01  cnf(c_0,plain,
% 4.18/1.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 4.18/1.01      inference(cnf_transformation,[],[f57]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_28,negated_conjecture,
% 4.18/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 4.18/1.01      inference(cnf_transformation,[],[f88]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1278,plain,
% 4.18/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_18,plain,
% 4.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.18/1.01      | v2_struct_0(X1)
% 4.18/1.01      | ~ l1_pre_topc(X1)
% 4.18/1.01      | v1_xboole_0(X0)
% 4.18/1.01      | u1_struct_0(sK1(X1,X0)) = X0 ),
% 4.18/1.01      inference(cnf_transformation,[],[f77]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1286,plain,
% 4.18/1.01      ( u1_struct_0(sK1(X0,X1)) = X1
% 4.18/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.18/1.01      | v2_struct_0(X0) = iProver_top
% 4.18/1.01      | l1_pre_topc(X0) != iProver_top
% 4.18/1.01      | v1_xboole_0(X1) = iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_3228,plain,
% 4.18/1.01      ( u1_struct_0(sK1(sK3,sK4)) = sK4
% 4.18/1.01      | v2_struct_0(sK3) = iProver_top
% 4.18/1.01      | l1_pre_topc(sK3) != iProver_top
% 4.18/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_1278,c_1286]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_32,negated_conjecture,
% 4.18/1.01      ( ~ v2_struct_0(sK3) ),
% 4.18/1.01      inference(cnf_transformation,[],[f84]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_33,plain,
% 4.18/1.01      ( v2_struct_0(sK3) != iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_29,negated_conjecture,
% 4.18/1.01      ( l1_pre_topc(sK3) ),
% 4.18/1.01      inference(cnf_transformation,[],[f87]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_36,plain,
% 4.18/1.01      ( l1_pre_topc(sK3) = iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_3657,plain,
% 4.18/1.01      ( u1_struct_0(sK1(sK3,sK4)) = sK4
% 4.18/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 4.18/1.01      inference(global_propositional_subsumption,
% 4.18/1.01                [status(thm)],
% 4.18/1.01                [c_3228,c_33,c_36]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_6,plain,
% 4.18/1.01      ( r1_tarski(X0,X0) ),
% 4.18/1.01      inference(cnf_transformation,[],[f91]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1294,plain,
% 4.18/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_2,plain,
% 4.18/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 4.18/1.01      inference(cnf_transformation,[],[f59]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1297,plain,
% 4.18/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 4.18/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_14,plain,
% 4.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.18/1.01      | ~ r2_hidden(X2,X0)
% 4.18/1.01      | ~ v1_xboole_0(X1) ),
% 4.18/1.01      inference(cnf_transformation,[],[f71]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_12,plain,
% 4.18/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.18/1.01      inference(cnf_transformation,[],[f70]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_203,plain,
% 4.18/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 4.18/1.01      inference(prop_impl,[status(thm)],[c_12]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_204,plain,
% 4.18/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.18/1.01      inference(renaming,[status(thm)],[c_203]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_264,plain,
% 4.18/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 4.18/1.01      inference(bin_hyper_res,[status(thm)],[c_14,c_204]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1271,plain,
% 4.18/1.01      ( r2_hidden(X0,X1) != iProver_top
% 4.18/1.01      | r1_tarski(X1,X2) != iProver_top
% 4.18/1.01      | v1_xboole_0(X2) != iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_264]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_2932,plain,
% 4.18/1.01      ( r1_tarski(X0,X1) != iProver_top
% 4.18/1.01      | r1_tarski(X0,X2) = iProver_top
% 4.18/1.01      | v1_xboole_0(X1) != iProver_top ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_1297,c_1271]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_3032,plain,
% 4.18/1.01      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_1294,c_2932]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_7,plain,
% 4.18/1.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 4.18/1.01      inference(cnf_transformation,[],[f64]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1293,plain,
% 4.18/1.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_4135,plain,
% 4.18/1.01      ( k3_xboole_0(X0,X1) = X0 | v1_xboole_0(X0) != iProver_top ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_3032,c_1293]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_4385,plain,
% 4.18/1.01      ( k3_xboole_0(sK4,X0) = sK4 | u1_struct_0(sK1(sK3,sK4)) = sK4 ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_3657,c_4135]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_10,plain,
% 4.18/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 4.18/1.01      inference(cnf_transformation,[],[f67]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1292,plain,
% 4.18/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_9,plain,
% 4.18/1.01      ( k2_subset_1(X0) = X0 ),
% 4.18/1.01      inference(cnf_transformation,[],[f66]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1315,plain,
% 4.18/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.18/1.01      inference(light_normalisation,[status(thm)],[c_1292,c_9]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_3229,plain,
% 4.18/1.01      ( u1_struct_0(sK1(X0,u1_struct_0(X0))) = u1_struct_0(X0)
% 4.18/1.01      | v2_struct_0(X0) = iProver_top
% 4.18/1.01      | l1_pre_topc(X0) != iProver_top
% 4.18/1.01      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_1315,c_1286]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_7717,plain,
% 4.18/1.01      ( k3_xboole_0(sK4,X0) = sK4
% 4.18/1.01      | u1_struct_0(sK1(sK1(sK3,sK4),u1_struct_0(sK1(sK3,sK4)))) = u1_struct_0(sK1(sK3,sK4))
% 4.18/1.01      | v2_struct_0(sK1(sK3,sK4)) = iProver_top
% 4.18/1.01      | l1_pre_topc(sK1(sK3,sK4)) != iProver_top
% 4.18/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_4385,c_3229]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_27,negated_conjecture,
% 4.18/1.01      ( ~ v2_tex_2(sK4,sK3) ),
% 4.18/1.01      inference(cnf_transformation,[],[f89]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_38,plain,
% 4.18/1.01      ( v2_tex_2(sK4,sK3) != iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_92,plain,
% 4.18/1.01      ( r1_tarski(sK3,sK3) ),
% 4.18/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_4,plain,
% 4.18/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 4.18/1.01      inference(cnf_transformation,[],[f63]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_96,plain,
% 4.18/1.01      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 4.18/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_562,plain,( X0 = X0 ),theory(equality) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_2378,plain,
% 4.18/1.01      ( sK4 = sK4 ),
% 4.18/1.01      inference(instantiation,[status(thm)],[c_562]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_20,plain,
% 4.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.18/1.01      | v2_struct_0(X1)
% 4.18/1.01      | ~ v2_struct_0(sK1(X1,X0))
% 4.18/1.01      | ~ l1_pre_topc(X1)
% 4.18/1.01      | v1_xboole_0(X0) ),
% 4.18/1.01      inference(cnf_transformation,[],[f75]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1284,plain,
% 4.18/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.18/1.01      | v2_struct_0(X1) = iProver_top
% 4.18/1.01      | v2_struct_0(sK1(X1,X0)) != iProver_top
% 4.18/1.01      | l1_pre_topc(X1) != iProver_top
% 4.18/1.01      | v1_xboole_0(X0) = iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_3349,plain,
% 4.18/1.01      ( v2_struct_0(sK1(sK3,sK4)) != iProver_top
% 4.18/1.01      | v2_struct_0(sK3) = iProver_top
% 4.18/1.01      | l1_pre_topc(sK3) != iProver_top
% 4.18/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_1278,c_1284]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_3664,plain,
% 4.18/1.01      ( v2_struct_0(sK1(sK3,sK4)) != iProver_top
% 4.18/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 4.18/1.01      inference(global_propositional_subsumption,
% 4.18/1.01                [status(thm)],
% 4.18/1.01                [c_3349,c_33,c_36]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_19,plain,
% 4.18/1.01      ( m1_pre_topc(sK1(X0,X1),X0)
% 4.18/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 4.18/1.01      | v2_struct_0(X0)
% 4.18/1.01      | ~ l1_pre_topc(X0)
% 4.18/1.01      | v1_xboole_0(X1) ),
% 4.18/1.01      inference(cnf_transformation,[],[f76]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1285,plain,
% 4.18/1.01      ( m1_pre_topc(sK1(X0,X1),X0) = iProver_top
% 4.18/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.18/1.01      | v2_struct_0(X0) = iProver_top
% 4.18/1.01      | l1_pre_topc(X0) != iProver_top
% 4.18/1.01      | v1_xboole_0(X1) = iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_3405,plain,
% 4.18/1.01      ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
% 4.18/1.01      | v2_struct_0(sK3) = iProver_top
% 4.18/1.01      | l1_pre_topc(sK3) != iProver_top
% 4.18/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_1278,c_1285]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_3845,plain,
% 4.18/1.01      ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
% 4.18/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 4.18/1.01      inference(global_propositional_subsumption,
% 4.18/1.01                [status(thm)],
% 4.18/1.01                [c_3405,c_33,c_36]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_563,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_2381,plain,
% 4.18/1.01      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 4.18/1.01      inference(instantiation,[status(thm)],[c_563]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_2992,plain,
% 4.18/1.01      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 4.18/1.01      inference(instantiation,[status(thm)],[c_2381]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_5737,plain,
% 4.18/1.01      ( u1_struct_0(sK1(sK3,sK4)) != sK4
% 4.18/1.01      | sK4 = u1_struct_0(sK1(sK3,sK4))
% 4.18/1.01      | sK4 != sK4 ),
% 4.18/1.01      inference(instantiation,[status(thm)],[c_2992]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_21,plain,
% 4.18/1.01      ( v2_tex_2(u1_struct_0(X0),X1)
% 4.18/1.01      | ~ m1_pre_topc(X0,X1)
% 4.18/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.18/1.01      | v2_struct_0(X1)
% 4.18/1.01      | v2_struct_0(X0)
% 4.18/1.01      | ~ v1_tdlat_3(X0)
% 4.18/1.01      | ~ l1_pre_topc(X1) ),
% 4.18/1.01      inference(cnf_transformation,[],[f92]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_15,plain,
% 4.18/1.01      ( ~ m1_pre_topc(X0,X1)
% 4.18/1.01      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.18/1.01      | ~ l1_pre_topc(X1) ),
% 4.18/1.01      inference(cnf_transformation,[],[f72]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_331,plain,
% 4.18/1.01      ( ~ m1_pre_topc(X0,X1)
% 4.18/1.01      | v2_tex_2(u1_struct_0(X0),X1)
% 4.18/1.01      | v2_struct_0(X1)
% 4.18/1.01      | v2_struct_0(X0)
% 4.18/1.01      | ~ v1_tdlat_3(X0)
% 4.18/1.01      | ~ l1_pre_topc(X1) ),
% 4.18/1.01      inference(global_propositional_subsumption,
% 4.18/1.01                [status(thm)],
% 4.18/1.01                [c_21,c_15]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_332,plain,
% 4.18/1.01      ( v2_tex_2(u1_struct_0(X0),X1)
% 4.18/1.01      | ~ m1_pre_topc(X0,X1)
% 4.18/1.01      | v2_struct_0(X0)
% 4.18/1.01      | v2_struct_0(X1)
% 4.18/1.01      | ~ v1_tdlat_3(X0)
% 4.18/1.01      | ~ l1_pre_topc(X1) ),
% 4.18/1.01      inference(renaming,[status(thm)],[c_331]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_5801,plain,
% 4.18/1.01      ( v2_tex_2(u1_struct_0(sK1(sK3,sK4)),sK3)
% 4.18/1.01      | ~ m1_pre_topc(sK1(sK3,sK4),sK3)
% 4.18/1.01      | v2_struct_0(sK1(sK3,sK4))
% 4.18/1.01      | v2_struct_0(sK3)
% 4.18/1.01      | ~ v1_tdlat_3(sK1(sK3,sK4))
% 4.18/1.01      | ~ l1_pre_topc(sK3) ),
% 4.18/1.01      inference(instantiation,[status(thm)],[c_332]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_5805,plain,
% 4.18/1.01      ( v2_tex_2(u1_struct_0(sK1(sK3,sK4)),sK3) = iProver_top
% 4.18/1.01      | m1_pre_topc(sK1(sK3,sK4),sK3) != iProver_top
% 4.18/1.01      | v2_struct_0(sK1(sK3,sK4)) = iProver_top
% 4.18/1.01      | v2_struct_0(sK3) = iProver_top
% 4.18/1.01      | v1_tdlat_3(sK1(sK3,sK4)) != iProver_top
% 4.18/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_5801]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_17,plain,
% 4.18/1.01      ( ~ m1_pre_topc(X0,X1)
% 4.18/1.01      | v2_struct_0(X1)
% 4.18/1.01      | ~ v1_tdlat_3(X1)
% 4.18/1.01      | v1_tdlat_3(X0)
% 4.18/1.01      | ~ v2_pre_topc(X1)
% 4.18/1.01      | ~ l1_pre_topc(X1) ),
% 4.18/1.01      inference(cnf_transformation,[],[f74]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1287,plain,
% 4.18/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 4.18/1.01      | v2_struct_0(X1) = iProver_top
% 4.18/1.01      | v1_tdlat_3(X1) != iProver_top
% 4.18/1.01      | v1_tdlat_3(X0) = iProver_top
% 4.18/1.01      | v2_pre_topc(X1) != iProver_top
% 4.18/1.01      | l1_pre_topc(X1) != iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_16,plain,
% 4.18/1.01      ( ~ v1_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 4.18/1.01      inference(cnf_transformation,[],[f73]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1288,plain,
% 4.18/1.01      ( v1_tdlat_3(X0) != iProver_top
% 4.18/1.01      | v2_pre_topc(X0) = iProver_top
% 4.18/1.01      | l1_pre_topc(X0) != iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1414,plain,
% 4.18/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 4.18/1.01      | v2_struct_0(X1) = iProver_top
% 4.18/1.01      | v1_tdlat_3(X1) != iProver_top
% 4.18/1.01      | v1_tdlat_3(X0) = iProver_top
% 4.18/1.01      | l1_pre_topc(X1) != iProver_top ),
% 4.18/1.01      inference(forward_subsumption_resolution,
% 4.18/1.01                [status(thm)],
% 4.18/1.01                [c_1287,c_1288]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_6201,plain,
% 4.18/1.01      ( v2_struct_0(sK3) = iProver_top
% 4.18/1.01      | v1_tdlat_3(sK1(sK3,sK4)) = iProver_top
% 4.18/1.01      | v1_tdlat_3(sK3) != iProver_top
% 4.18/1.01      | l1_pre_topc(sK3) != iProver_top
% 4.18/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_3845,c_1414]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_30,negated_conjecture,
% 4.18/1.01      ( v1_tdlat_3(sK3) ),
% 4.18/1.01      inference(cnf_transformation,[],[f86]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_35,plain,
% 4.18/1.01      ( v1_tdlat_3(sK3) = iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_7013,plain,
% 4.18/1.01      ( v1_tdlat_3(sK1(sK3,sK4)) = iProver_top
% 4.18/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 4.18/1.01      inference(global_propositional_subsumption,
% 4.18/1.01                [status(thm)],
% 4.18/1.01                [c_6201,c_33,c_35,c_36]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_575,plain,
% 4.18/1.01      ( ~ v2_tex_2(X0,X1) | v2_tex_2(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.18/1.01      theory(equality) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_2201,plain,
% 4.18/1.01      ( ~ v2_tex_2(X0,X1) | v2_tex_2(sK4,sK3) | sK3 != X1 | sK4 != X0 ),
% 4.18/1.01      inference(instantiation,[status(thm)],[c_575]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_11082,plain,
% 4.18/1.01      ( ~ v2_tex_2(u1_struct_0(sK1(sK3,sK4)),X0)
% 4.18/1.01      | v2_tex_2(sK4,sK3)
% 4.18/1.01      | sK3 != X0
% 4.18/1.01      | sK4 != u1_struct_0(sK1(sK3,sK4)) ),
% 4.18/1.01      inference(instantiation,[status(thm)],[c_2201]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_11083,plain,
% 4.18/1.01      ( sK3 != X0
% 4.18/1.01      | sK4 != u1_struct_0(sK1(sK3,sK4))
% 4.18/1.01      | v2_tex_2(u1_struct_0(sK1(sK3,sK4)),X0) != iProver_top
% 4.18/1.01      | v2_tex_2(sK4,sK3) = iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_11082]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_11085,plain,
% 4.18/1.01      ( sK3 != sK3
% 4.18/1.01      | sK4 != u1_struct_0(sK1(sK3,sK4))
% 4.18/1.01      | v2_tex_2(u1_struct_0(sK1(sK3,sK4)),sK3) != iProver_top
% 4.18/1.01      | v2_tex_2(sK4,sK3) = iProver_top ),
% 4.18/1.01      inference(instantiation,[status(thm)],[c_11083]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_11490,plain,
% 4.18/1.01      ( v1_xboole_0(sK4) = iProver_top ),
% 4.18/1.01      inference(global_propositional_subsumption,
% 4.18/1.01                [status(thm)],
% 4.18/1.01                [c_7717,c_33,c_36,c_38,c_92,c_96,c_2378,c_3657,c_3664,
% 4.18/1.01                 c_3845,c_5737,c_5805,c_7013,c_11085]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_11495,plain,
% 4.18/1.01      ( k3_xboole_0(sK4,X0) = sK4 ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_11490,c_4135]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_14692,plain,
% 4.18/1.01      ( k3_xboole_0(X0,sK4) = sK4 ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_0,c_11495]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_13,plain,
% 4.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.18/1.01      inference(cnf_transformation,[],[f69]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1290,plain,
% 4.18/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.18/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1924,plain,
% 4.18/1.01      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_1278,c_1290]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_8,plain,
% 4.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.18/1.01      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 4.18/1.01      inference(cnf_transformation,[],[f65]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_260,plain,
% 4.18/1.01      ( ~ r1_tarski(X0,X1)
% 4.18/1.01      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 4.18/1.01      inference(bin_hyper_res,[status(thm)],[c_8,c_204]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1273,plain,
% 4.18/1.01      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 4.18/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_260]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_2713,plain,
% 4.18/1.01      ( k9_subset_1(u1_struct_0(sK3),sK4,X0) = k9_subset_1(u1_struct_0(sK3),X0,sK4) ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_1924,c_1273]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_11,plain,
% 4.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.18/1.01      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 4.18/1.01      inference(cnf_transformation,[],[f68]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_261,plain,
% 4.18/1.01      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 4.18/1.01      inference(bin_hyper_res,[status(thm)],[c_11,c_204]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1272,plain,
% 4.18/1.01      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 4.18/1.01      | r1_tarski(X2,X0) != iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_261]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_2210,plain,
% 4.18/1.01      ( k9_subset_1(u1_struct_0(sK3),X0,sK4) = k3_xboole_0(X0,sK4) ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_1924,c_1272]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_2715,plain,
% 4.18/1.01      ( k9_subset_1(u1_struct_0(sK3),sK4,X0) = k3_xboole_0(X0,sK4) ),
% 4.18/1.01      inference(light_normalisation,[status(thm)],[c_2713,c_2210]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_15051,plain,
% 4.18/1.01      ( k9_subset_1(u1_struct_0(sK3),sK4,X0) = sK4 ),
% 4.18/1.01      inference(demodulation,[status(thm)],[c_14692,c_2715]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_23,plain,
% 4.18/1.01      ( v2_tex_2(X0,X1)
% 4.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.18/1.01      | v2_struct_0(X1)
% 4.18/1.01      | ~ v2_pre_topc(X1)
% 4.18/1.01      | ~ l1_pre_topc(X1)
% 4.18/1.01      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,sK2(X1,X0))) != sK2(X1,X0) ),
% 4.18/1.01      inference(cnf_transformation,[],[f83]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1283,plain,
% 4.18/1.01      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
% 4.18/1.01      | v2_tex_2(X1,X0) = iProver_top
% 4.18/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.18/1.01      | v2_struct_0(X0) = iProver_top
% 4.18/1.01      | v2_pre_topc(X0) != iProver_top
% 4.18/1.01      | l1_pre_topc(X0) != iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_15213,plain,
% 4.18/1.01      ( sK2(sK3,sK4) != sK4
% 4.18/1.01      | v2_tex_2(sK4,sK3) = iProver_top
% 4.18/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 4.18/1.01      | v2_struct_0(sK3) = iProver_top
% 4.18/1.01      | v2_pre_topc(sK3) != iProver_top
% 4.18/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_15051,c_1283]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1289,plain,
% 4.18/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 4.18/1.01      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 4.18/1.01      | l1_pre_topc(X1) != iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_3192,plain,
% 4.18/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 4.18/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 4.18/1.01      | l1_pre_topc(X1) != iProver_top ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_1289,c_1290]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_6745,plain,
% 4.18/1.01      ( k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X0)
% 4.18/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 4.18/1.01      | l1_pre_topc(X1) != iProver_top ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_3192,c_1293]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_7585,plain,
% 4.18/1.01      ( k3_xboole_0(u1_struct_0(sK1(sK3,sK4)),u1_struct_0(sK3)) = u1_struct_0(sK1(sK3,sK4))
% 4.18/1.01      | l1_pre_topc(sK3) != iProver_top
% 4.18/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_3845,c_6745]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_7981,plain,
% 4.18/1.01      ( k3_xboole_0(u1_struct_0(sK1(sK3,sK4)),u1_struct_0(sK3)) = u1_struct_0(sK1(sK3,sK4))
% 4.18/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 4.18/1.01      inference(global_propositional_subsumption,
% 4.18/1.01                [status(thm)],
% 4.18/1.01                [c_7585,c_36]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_24,plain,
% 4.18/1.01      ( v2_tex_2(X0,X1)
% 4.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.18/1.01      | r1_tarski(sK2(X1,X0),X0)
% 4.18/1.01      | v2_struct_0(X1)
% 4.18/1.01      | ~ v2_pre_topc(X1)
% 4.18/1.01      | ~ l1_pre_topc(X1) ),
% 4.18/1.01      inference(cnf_transformation,[],[f82]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1282,plain,
% 4.18/1.01      ( v2_tex_2(X0,X1) = iProver_top
% 4.18/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.18/1.01      | r1_tarski(sK2(X1,X0),X0) = iProver_top
% 4.18/1.01      | v2_struct_0(X1) = iProver_top
% 4.18/1.01      | v2_pre_topc(X1) != iProver_top
% 4.18/1.01      | l1_pre_topc(X1) != iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_5108,plain,
% 4.18/1.01      ( v2_tex_2(sK4,sK3) = iProver_top
% 4.18/1.01      | r1_tarski(sK2(sK3,sK4),sK4) = iProver_top
% 4.18/1.01      | v2_struct_0(sK3) = iProver_top
% 4.18/1.01      | v2_pre_topc(sK3) != iProver_top
% 4.18/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_1278,c_1282]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_31,negated_conjecture,
% 4.18/1.01      ( v2_pre_topc(sK3) ),
% 4.18/1.01      inference(cnf_transformation,[],[f85]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_34,plain,
% 4.18/1.01      ( v2_pre_topc(sK3) = iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_37,plain,
% 4.18/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1655,plain,
% 4.18/1.01      ( v2_tex_2(sK4,sK3)
% 4.18/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.18/1.01      | r1_tarski(sK2(sK3,sK4),sK4)
% 4.18/1.01      | v2_struct_0(sK3)
% 4.18/1.01      | ~ v2_pre_topc(sK3)
% 4.18/1.01      | ~ l1_pre_topc(sK3) ),
% 4.18/1.01      inference(instantiation,[status(thm)],[c_24]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1656,plain,
% 4.18/1.01      ( v2_tex_2(sK4,sK3) = iProver_top
% 4.18/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 4.18/1.01      | r1_tarski(sK2(sK3,sK4),sK4) = iProver_top
% 4.18/1.01      | v2_struct_0(sK3) = iProver_top
% 4.18/1.01      | v2_pre_topc(sK3) != iProver_top
% 4.18/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_1655]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_5486,plain,
% 4.18/1.01      ( r1_tarski(sK2(sK3,sK4),sK4) = iProver_top ),
% 4.18/1.01      inference(global_propositional_subsumption,
% 4.18/1.01                [status(thm)],
% 4.18/1.01                [c_5108,c_33,c_34,c_36,c_37,c_38,c_1656]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1295,plain,
% 4.18/1.01      ( X0 = X1
% 4.18/1.01      | r1_tarski(X1,X0) != iProver_top
% 4.18/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_4134,plain,
% 4.18/1.01      ( X0 = X1
% 4.18/1.01      | r1_tarski(X0,X1) != iProver_top
% 4.18/1.01      | v1_xboole_0(X1) != iProver_top ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_3032,c_1295]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_5491,plain,
% 4.18/1.01      ( sK2(sK3,sK4) = sK4 | v1_xboole_0(sK4) != iProver_top ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_5486,c_4134]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_7992,plain,
% 4.18/1.01      ( sK2(sK3,sK4) = sK4
% 4.18/1.01      | k3_xboole_0(u1_struct_0(sK1(sK3,sK4)),u1_struct_0(sK3)) = u1_struct_0(sK1(sK3,sK4)) ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_7981,c_5491]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_5494,plain,
% 4.18/1.01      ( k3_xboole_0(sK2(sK3,sK4),sK4) = sK2(sK3,sK4) ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_5486,c_1293]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_4399,plain,
% 4.18/1.01      ( k3_xboole_0(X0,sK4) = sK4 | u1_struct_0(sK1(sK3,sK4)) = sK4 ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_4385,c_0]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_5750,plain,
% 4.18/1.01      ( sK2(sK3,sK4) = sK4 | u1_struct_0(sK1(sK3,sK4)) = sK4 ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_5494,c_4399]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_1269,plain,
% 4.18/1.01      ( v2_tex_2(u1_struct_0(X0),X1) = iProver_top
% 4.18/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 4.18/1.01      | v2_struct_0(X1) = iProver_top
% 4.18/1.01      | v2_struct_0(X0) = iProver_top
% 4.18/1.01      | v1_tdlat_3(X0) != iProver_top
% 4.18/1.01      | l1_pre_topc(X1) != iProver_top ),
% 4.18/1.01      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_6301,plain,
% 4.18/1.01      ( sK2(sK3,sK4) = sK4
% 4.18/1.01      | v2_tex_2(sK4,X0) = iProver_top
% 4.18/1.01      | m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
% 4.18/1.01      | v2_struct_0(X0) = iProver_top
% 4.18/1.01      | v2_struct_0(sK1(sK3,sK4)) = iProver_top
% 4.18/1.01      | v1_tdlat_3(sK1(sK3,sK4)) != iProver_top
% 4.18/1.01      | l1_pre_topc(X0) != iProver_top ),
% 4.18/1.01      inference(superposition,[status(thm)],[c_5750,c_1269]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_6469,plain,
% 4.18/1.01      ( sK2(sK3,sK4) = sK4
% 4.18/1.01      | v2_tex_2(sK4,sK3) = iProver_top
% 4.18/1.01      | m1_pre_topc(sK1(sK3,sK4),sK3) != iProver_top
% 4.18/1.01      | v2_struct_0(sK1(sK3,sK4)) = iProver_top
% 4.18/1.01      | v2_struct_0(sK3) = iProver_top
% 4.18/1.01      | v1_tdlat_3(sK1(sK3,sK4)) != iProver_top
% 4.18/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 4.18/1.01      inference(instantiation,[status(thm)],[c_6301]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_8214,plain,
% 4.18/1.01      ( sK2(sK3,sK4) = sK4 ),
% 4.18/1.01      inference(global_propositional_subsumption,
% 4.18/1.01                [status(thm)],
% 4.18/1.01                [c_7992,c_33,c_36,c_38,c_3664,c_3845,c_5491,c_6469,
% 4.18/1.01                 c_7013]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_15221,plain,
% 4.18/1.01      ( sK4 != sK4
% 4.18/1.01      | v2_tex_2(sK4,sK3) = iProver_top
% 4.18/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 4.18/1.01      | v2_struct_0(sK3) = iProver_top
% 4.18/1.01      | v2_pre_topc(sK3) != iProver_top
% 4.18/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 4.18/1.01      inference(light_normalisation,[status(thm)],[c_15213,c_8214]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(c_15222,plain,
% 4.18/1.01      ( v2_tex_2(sK4,sK3) = iProver_top
% 4.18/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 4.18/1.01      | v2_struct_0(sK3) = iProver_top
% 4.18/1.01      | v2_pre_topc(sK3) != iProver_top
% 4.18/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 4.18/1.01      inference(equality_resolution_simp,[status(thm)],[c_15221]) ).
% 4.18/1.01  
% 4.18/1.01  cnf(contradiction,plain,
% 4.18/1.01      ( $false ),
% 4.18/1.01      inference(minisat,[status(thm)],[c_15222,c_38,c_37,c_36,c_34,c_33]) ).
% 4.18/1.01  
% 4.18/1.01  
% 4.18/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 4.18/1.01  
% 4.18/1.01  ------                               Statistics
% 4.18/1.01  
% 4.18/1.01  ------ Selected
% 4.18/1.01  
% 4.18/1.01  total_time:                             0.48
% 4.18/1.01  
%------------------------------------------------------------------------------
