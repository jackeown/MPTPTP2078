%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:42 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 920 expanded)
%              Number of clauses        :   82 ( 269 expanded)
%              Number of leaves         :   21 ( 220 expanded)
%              Depth                    :   21
%              Number of atoms          :  522 (4003 expanded)
%              Number of equality atoms :  156 ( 408 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ~ v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f57,f56])).

fof(f89,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f75,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f88,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

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

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f90,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f18,axiom,(
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

fof(f24,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f25,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v1_tdlat_3(X1) ) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

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

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f86,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f87,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f74,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f69,f66])).

fof(f21,axiom,(
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

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ( ~ v2_tex_2(X2,X0)
                & ~ v2_tex_2(X1,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ( ~ v2_tex_2(X2,X0)
                & ~ v2_tex_2(X1,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_tdlat_3(X0)
      | u1_struct_0(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f97,plain,(
    ! [X0] :
      ( v2_tex_2(u1_struct_0(X0),X0)
      | ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

cnf(c_8,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1586,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1608,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1586,c_7])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1574,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1581,plain,
    ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2926,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1574,c_1581])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1834,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3207,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2926,c_27,c_26,c_1834])).

cnf(c_19,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_168,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_tex_2(u1_struct_0(X0),X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_16])).

cnf(c_169,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_168])).

cnf(c_1569,plain,
    ( v2_tex_2(u1_struct_0(X0),X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_169])).

cnf(c_3213,plain,
    ( v2_tex_2(sK1,X0) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,sK1),X0) != iProver_top
    | v1_tdlat_3(k1_pre_topc(sK0,sK1)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k1_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3207,c_1569])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_31,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_34,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_35,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_36,plain,
    ( v2_tex_2(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_11,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1827,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1828,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1827])).

cnf(c_3259,plain,
    ( v2_tex_2(sK1,sK0) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) != iProver_top
    | v1_tdlat_3(k1_pre_topc(sK0,sK1)) != iProver_top
    | v2_struct_0(k1_pre_topc(sK0,sK1)) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3213])).

cnf(c_1583,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3068,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1574,c_1583])).

cnf(c_3265,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3068,c_34,c_35,c_1828])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X1)
    | v1_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_437,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_438,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | v1_tdlat_3(X0)
    | ~ v1_tdlat_3(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_28,negated_conjecture,
    ( v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_440,plain,
    ( v1_tdlat_3(X0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_30,c_28,c_27])).

cnf(c_441,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | v1_tdlat_3(X0) ),
    inference(renaming,[status(thm)],[c_440])).

cnf(c_1566,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | v1_tdlat_3(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_3272,plain,
    ( v1_tdlat_3(k1_pre_topc(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3265,c_1566])).

cnf(c_4403,plain,
    ( v2_struct_0(k1_pre_topc(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3213,c_31,c_34,c_35,c_36,c_1828,c_3259,c_3272])).

cnf(c_12,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_14,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_385,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_386,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k1_xboole_0 = u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_402,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_386])).

cnf(c_1568,plain,
    ( u1_struct_0(X0) = k1_xboole_0
    | v2_struct_0(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_4408,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) = k1_xboole_0
    | l1_pre_topc(k1_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4403,c_1568])).

cnf(c_4409,plain,
    ( sK1 = k1_xboole_0
    | l1_pre_topc(k1_pre_topc(sK0,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4408,c_3207])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1582,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3270,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3265,c_1582])).

cnf(c_4412,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4409,c_34,c_3270])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1585,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2835,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK1)) = k9_subset_1(u1_struct_0(sK0),X0,sK1) ),
    inference(superposition,[status(thm)],[c_1574,c_1585])).

cnf(c_24,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(k9_subset_1(u1_struct_0(X1),X0,X2),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1576,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v2_tex_2(k9_subset_1(u1_struct_0(X1),X0,X2),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3808,plain,
    ( v2_tex_2(X0,sK0) != iProver_top
    | v2_tex_2(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2835,c_1576])).

cnf(c_4247,plain,
    ( v2_tex_2(X0,sK0) != iProver_top
    | v2_tex_2(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3808,c_34,c_35])).

cnf(c_4419,plain,
    ( v2_tex_2(X0,sK0) != iProver_top
    | v2_tex_2(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4412,c_4247])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1590,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1589,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2243,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1590,c_1589])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1587,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2459,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1590,c_1587])).

cnf(c_2460,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2459,c_2243])).

cnf(c_4472,plain,
    ( v2_tex_2(X0,sK0) != iProver_top
    | v2_tex_2(k1_xboole_0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4419,c_2243,c_2460])).

cnf(c_1575,plain,
    ( v2_tex_2(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4433,plain,
    ( v2_tex_2(k1_xboole_0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4412,c_1575])).

cnf(c_12082,plain,
    ( v2_tex_2(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4472,c_4433])).

cnf(c_12092,plain,
    ( v2_tex_2(u1_struct_0(sK0),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1608,c_12082])).

cnf(c_21,plain,
    ( v2_tex_2(u1_struct_0(X0),X0)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1579,plain,
    ( v2_tex_2(u1_struct_0(X0),X0) = iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1692,plain,
    ( v2_tex_2(u1_struct_0(X0),X0) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1579,c_1608])).

cnf(c_1765,plain,
    ( v2_tex_2(u1_struct_0(sK0),sK0) = iProver_top
    | v1_tdlat_3(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1692])).

cnf(c_33,plain,
    ( v1_tdlat_3(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12092,c_1765,c_34,c_33,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.03/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.04  
% 3.03/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.03/1.04  
% 3.03/1.04  ------  iProver source info
% 3.03/1.04  
% 3.03/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.03/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.03/1.04  git: non_committed_changes: false
% 3.03/1.04  git: last_make_outside_of_git: false
% 3.03/1.04  
% 3.03/1.04  ------ 
% 3.03/1.04  
% 3.03/1.04  ------ Input Options
% 3.03/1.04  
% 3.03/1.04  --out_options                           all
% 3.03/1.04  --tptp_safe_out                         true
% 3.03/1.04  --problem_path                          ""
% 3.03/1.04  --include_path                          ""
% 3.03/1.04  --clausifier                            res/vclausify_rel
% 3.03/1.04  --clausifier_options                    --mode clausify
% 3.03/1.04  --stdin                                 false
% 3.03/1.04  --stats_out                             all
% 3.03/1.04  
% 3.03/1.04  ------ General Options
% 3.03/1.04  
% 3.03/1.04  --fof                                   false
% 3.03/1.04  --time_out_real                         305.
% 3.03/1.04  --time_out_virtual                      -1.
% 3.03/1.04  --symbol_type_check                     false
% 3.03/1.04  --clausify_out                          false
% 3.03/1.04  --sig_cnt_out                           false
% 3.03/1.04  --trig_cnt_out                          false
% 3.03/1.04  --trig_cnt_out_tolerance                1.
% 3.03/1.04  --trig_cnt_out_sk_spl                   false
% 3.03/1.04  --abstr_cl_out                          false
% 3.03/1.04  
% 3.03/1.04  ------ Global Options
% 3.03/1.04  
% 3.03/1.04  --schedule                              default
% 3.03/1.04  --add_important_lit                     false
% 3.03/1.04  --prop_solver_per_cl                    1000
% 3.03/1.04  --min_unsat_core                        false
% 3.03/1.04  --soft_assumptions                      false
% 3.03/1.04  --soft_lemma_size                       3
% 3.03/1.04  --prop_impl_unit_size                   0
% 3.03/1.04  --prop_impl_unit                        []
% 3.03/1.04  --share_sel_clauses                     true
% 3.03/1.04  --reset_solvers                         false
% 3.03/1.04  --bc_imp_inh                            [conj_cone]
% 3.03/1.04  --conj_cone_tolerance                   3.
% 3.03/1.04  --extra_neg_conj                        none
% 3.03/1.04  --large_theory_mode                     true
% 3.03/1.04  --prolific_symb_bound                   200
% 3.03/1.04  --lt_threshold                          2000
% 3.03/1.04  --clause_weak_htbl                      true
% 3.03/1.04  --gc_record_bc_elim                     false
% 3.03/1.04  
% 3.03/1.04  ------ Preprocessing Options
% 3.03/1.04  
% 3.03/1.04  --preprocessing_flag                    true
% 3.03/1.04  --time_out_prep_mult                    0.1
% 3.03/1.04  --splitting_mode                        input
% 3.03/1.04  --splitting_grd                         true
% 3.03/1.04  --splitting_cvd                         false
% 3.03/1.04  --splitting_cvd_svl                     false
% 3.03/1.04  --splitting_nvd                         32
% 3.03/1.04  --sub_typing                            true
% 3.03/1.04  --prep_gs_sim                           true
% 3.03/1.04  --prep_unflatten                        true
% 3.03/1.04  --prep_res_sim                          true
% 3.03/1.04  --prep_upred                            true
% 3.03/1.04  --prep_sem_filter                       exhaustive
% 3.03/1.04  --prep_sem_filter_out                   false
% 3.03/1.04  --pred_elim                             true
% 3.03/1.04  --res_sim_input                         true
% 3.03/1.04  --eq_ax_congr_red                       true
% 3.03/1.04  --pure_diseq_elim                       true
% 3.03/1.04  --brand_transform                       false
% 3.03/1.04  --non_eq_to_eq                          false
% 3.03/1.04  --prep_def_merge                        true
% 3.03/1.04  --prep_def_merge_prop_impl              false
% 3.03/1.04  --prep_def_merge_mbd                    true
% 3.03/1.04  --prep_def_merge_tr_red                 false
% 3.03/1.04  --prep_def_merge_tr_cl                  false
% 3.03/1.04  --smt_preprocessing                     true
% 3.03/1.04  --smt_ac_axioms                         fast
% 3.03/1.04  --preprocessed_out                      false
% 3.03/1.04  --preprocessed_stats                    false
% 3.03/1.04  
% 3.03/1.04  ------ Abstraction refinement Options
% 3.03/1.04  
% 3.03/1.04  --abstr_ref                             []
% 3.03/1.04  --abstr_ref_prep                        false
% 3.03/1.04  --abstr_ref_until_sat                   false
% 3.03/1.04  --abstr_ref_sig_restrict                funpre
% 3.03/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/1.04  --abstr_ref_under                       []
% 3.03/1.04  
% 3.03/1.04  ------ SAT Options
% 3.03/1.04  
% 3.03/1.04  --sat_mode                              false
% 3.03/1.04  --sat_fm_restart_options                ""
% 3.03/1.04  --sat_gr_def                            false
% 3.03/1.04  --sat_epr_types                         true
% 3.03/1.04  --sat_non_cyclic_types                  false
% 3.03/1.04  --sat_finite_models                     false
% 3.03/1.04  --sat_fm_lemmas                         false
% 3.03/1.04  --sat_fm_prep                           false
% 3.03/1.04  --sat_fm_uc_incr                        true
% 3.03/1.04  --sat_out_model                         small
% 3.03/1.04  --sat_out_clauses                       false
% 3.03/1.04  
% 3.03/1.04  ------ QBF Options
% 3.03/1.04  
% 3.03/1.04  --qbf_mode                              false
% 3.03/1.04  --qbf_elim_univ                         false
% 3.03/1.04  --qbf_dom_inst                          none
% 3.03/1.04  --qbf_dom_pre_inst                      false
% 3.03/1.04  --qbf_sk_in                             false
% 3.03/1.04  --qbf_pred_elim                         true
% 3.03/1.04  --qbf_split                             512
% 3.03/1.04  
% 3.03/1.04  ------ BMC1 Options
% 3.03/1.04  
% 3.03/1.04  --bmc1_incremental                      false
% 3.03/1.04  --bmc1_axioms                           reachable_all
% 3.03/1.04  --bmc1_min_bound                        0
% 3.03/1.04  --bmc1_max_bound                        -1
% 3.03/1.04  --bmc1_max_bound_default                -1
% 3.03/1.04  --bmc1_symbol_reachability              true
% 3.03/1.04  --bmc1_property_lemmas                  false
% 3.03/1.04  --bmc1_k_induction                      false
% 3.03/1.04  --bmc1_non_equiv_states                 false
% 3.03/1.04  --bmc1_deadlock                         false
% 3.03/1.04  --bmc1_ucm                              false
% 3.03/1.04  --bmc1_add_unsat_core                   none
% 3.03/1.04  --bmc1_unsat_core_children              false
% 3.03/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/1.04  --bmc1_out_stat                         full
% 3.03/1.04  --bmc1_ground_init                      false
% 3.03/1.04  --bmc1_pre_inst_next_state              false
% 3.03/1.04  --bmc1_pre_inst_state                   false
% 3.03/1.04  --bmc1_pre_inst_reach_state             false
% 3.03/1.04  --bmc1_out_unsat_core                   false
% 3.03/1.04  --bmc1_aig_witness_out                  false
% 3.03/1.04  --bmc1_verbose                          false
% 3.03/1.04  --bmc1_dump_clauses_tptp                false
% 3.03/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.03/1.04  --bmc1_dump_file                        -
% 3.03/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.03/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.03/1.04  --bmc1_ucm_extend_mode                  1
% 3.03/1.04  --bmc1_ucm_init_mode                    2
% 3.03/1.04  --bmc1_ucm_cone_mode                    none
% 3.03/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.03/1.04  --bmc1_ucm_relax_model                  4
% 3.03/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.03/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/1.04  --bmc1_ucm_layered_model                none
% 3.03/1.04  --bmc1_ucm_max_lemma_size               10
% 3.03/1.04  
% 3.03/1.04  ------ AIG Options
% 3.03/1.04  
% 3.03/1.04  --aig_mode                              false
% 3.03/1.04  
% 3.03/1.04  ------ Instantiation Options
% 3.03/1.04  
% 3.03/1.04  --instantiation_flag                    true
% 3.03/1.04  --inst_sos_flag                         false
% 3.03/1.04  --inst_sos_phase                        true
% 3.03/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/1.04  --inst_lit_sel_side                     num_symb
% 3.03/1.04  --inst_solver_per_active                1400
% 3.03/1.04  --inst_solver_calls_frac                1.
% 3.03/1.04  --inst_passive_queue_type               priority_queues
% 3.03/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/1.04  --inst_passive_queues_freq              [25;2]
% 3.03/1.04  --inst_dismatching                      true
% 3.03/1.04  --inst_eager_unprocessed_to_passive     true
% 3.03/1.04  --inst_prop_sim_given                   true
% 3.03/1.04  --inst_prop_sim_new                     false
% 3.03/1.04  --inst_subs_new                         false
% 3.03/1.04  --inst_eq_res_simp                      false
% 3.03/1.04  --inst_subs_given                       false
% 3.03/1.04  --inst_orphan_elimination               true
% 3.03/1.04  --inst_learning_loop_flag               true
% 3.03/1.04  --inst_learning_start                   3000
% 3.03/1.04  --inst_learning_factor                  2
% 3.03/1.04  --inst_start_prop_sim_after_learn       3
% 3.03/1.04  --inst_sel_renew                        solver
% 3.03/1.04  --inst_lit_activity_flag                true
% 3.03/1.04  --inst_restr_to_given                   false
% 3.03/1.04  --inst_activity_threshold               500
% 3.03/1.04  --inst_out_proof                        true
% 3.03/1.04  
% 3.03/1.04  ------ Resolution Options
% 3.03/1.04  
% 3.03/1.04  --resolution_flag                       true
% 3.03/1.04  --res_lit_sel                           adaptive
% 3.03/1.04  --res_lit_sel_side                      none
% 3.03/1.04  --res_ordering                          kbo
% 3.03/1.04  --res_to_prop_solver                    active
% 3.03/1.04  --res_prop_simpl_new                    false
% 3.03/1.04  --res_prop_simpl_given                  true
% 3.03/1.04  --res_passive_queue_type                priority_queues
% 3.03/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/1.04  --res_passive_queues_freq               [15;5]
% 3.03/1.04  --res_forward_subs                      full
% 3.03/1.04  --res_backward_subs                     full
% 3.03/1.04  --res_forward_subs_resolution           true
% 3.03/1.04  --res_backward_subs_resolution          true
% 3.03/1.04  --res_orphan_elimination                true
% 3.03/1.04  --res_time_limit                        2.
% 3.03/1.04  --res_out_proof                         true
% 3.03/1.04  
% 3.03/1.04  ------ Superposition Options
% 3.03/1.04  
% 3.03/1.04  --superposition_flag                    true
% 3.03/1.04  --sup_passive_queue_type                priority_queues
% 3.03/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.03/1.04  --demod_completeness_check              fast
% 3.03/1.04  --demod_use_ground                      true
% 3.03/1.04  --sup_to_prop_solver                    passive
% 3.03/1.04  --sup_prop_simpl_new                    true
% 3.03/1.04  --sup_prop_simpl_given                  true
% 3.03/1.04  --sup_fun_splitting                     false
% 3.03/1.04  --sup_smt_interval                      50000
% 3.03/1.04  
% 3.03/1.04  ------ Superposition Simplification Setup
% 3.03/1.04  
% 3.03/1.04  --sup_indices_passive                   []
% 3.03/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.04  --sup_full_bw                           [BwDemod]
% 3.03/1.04  --sup_immed_triv                        [TrivRules]
% 3.03/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.04  --sup_immed_bw_main                     []
% 3.03/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.04  
% 3.03/1.04  ------ Combination Options
% 3.03/1.04  
% 3.03/1.04  --comb_res_mult                         3
% 3.03/1.04  --comb_sup_mult                         2
% 3.03/1.04  --comb_inst_mult                        10
% 3.03/1.04  
% 3.03/1.04  ------ Debug Options
% 3.03/1.04  
% 3.03/1.04  --dbg_backtrace                         false
% 3.03/1.04  --dbg_dump_prop_clauses                 false
% 3.03/1.04  --dbg_dump_prop_clauses_file            -
% 3.03/1.04  --dbg_out_stat                          false
% 3.03/1.04  ------ Parsing...
% 3.03/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.03/1.04  
% 3.03/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.03/1.04  
% 3.03/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.03/1.04  
% 3.03/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.03/1.04  ------ Proving...
% 3.03/1.04  ------ Problem Properties 
% 3.03/1.04  
% 3.03/1.04  
% 3.03/1.04  clauses                                 27
% 3.03/1.04  conjectures                             5
% 3.03/1.04  EPR                                     9
% 3.03/1.04  Horn                                    22
% 3.03/1.04  unary                                   9
% 3.03/1.04  binary                                  5
% 3.03/1.04  lits                                    74
% 3.03/1.04  lits eq                                 8
% 3.03/1.04  fd_pure                                 0
% 3.03/1.04  fd_pseudo                               0
% 3.03/1.04  fd_cond                                 0
% 3.03/1.04  fd_pseudo_cond                          1
% 3.03/1.04  AC symbols                              0
% 3.03/1.04  
% 3.03/1.04  ------ Schedule dynamic 5 is on 
% 3.03/1.04  
% 3.03/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.03/1.04  
% 3.03/1.04  
% 3.03/1.04  ------ 
% 3.03/1.04  Current options:
% 3.03/1.04  ------ 
% 3.03/1.04  
% 3.03/1.04  ------ Input Options
% 3.03/1.04  
% 3.03/1.04  --out_options                           all
% 3.03/1.04  --tptp_safe_out                         true
% 3.03/1.04  --problem_path                          ""
% 3.03/1.04  --include_path                          ""
% 3.03/1.04  --clausifier                            res/vclausify_rel
% 3.03/1.04  --clausifier_options                    --mode clausify
% 3.03/1.04  --stdin                                 false
% 3.03/1.04  --stats_out                             all
% 3.03/1.04  
% 3.03/1.04  ------ General Options
% 3.03/1.04  
% 3.03/1.04  --fof                                   false
% 3.03/1.04  --time_out_real                         305.
% 3.03/1.04  --time_out_virtual                      -1.
% 3.03/1.04  --symbol_type_check                     false
% 3.03/1.04  --clausify_out                          false
% 3.03/1.04  --sig_cnt_out                           false
% 3.03/1.04  --trig_cnt_out                          false
% 3.03/1.04  --trig_cnt_out_tolerance                1.
% 3.03/1.04  --trig_cnt_out_sk_spl                   false
% 3.03/1.04  --abstr_cl_out                          false
% 3.03/1.04  
% 3.03/1.04  ------ Global Options
% 3.03/1.04  
% 3.03/1.04  --schedule                              default
% 3.03/1.04  --add_important_lit                     false
% 3.03/1.04  --prop_solver_per_cl                    1000
% 3.03/1.04  --min_unsat_core                        false
% 3.03/1.04  --soft_assumptions                      false
% 3.03/1.04  --soft_lemma_size                       3
% 3.03/1.04  --prop_impl_unit_size                   0
% 3.03/1.04  --prop_impl_unit                        []
% 3.03/1.04  --share_sel_clauses                     true
% 3.03/1.04  --reset_solvers                         false
% 3.03/1.04  --bc_imp_inh                            [conj_cone]
% 3.03/1.04  --conj_cone_tolerance                   3.
% 3.03/1.04  --extra_neg_conj                        none
% 3.03/1.04  --large_theory_mode                     true
% 3.03/1.04  --prolific_symb_bound                   200
% 3.03/1.04  --lt_threshold                          2000
% 3.03/1.04  --clause_weak_htbl                      true
% 3.03/1.04  --gc_record_bc_elim                     false
% 3.03/1.04  
% 3.03/1.04  ------ Preprocessing Options
% 3.03/1.04  
% 3.03/1.04  --preprocessing_flag                    true
% 3.03/1.04  --time_out_prep_mult                    0.1
% 3.03/1.04  --splitting_mode                        input
% 3.03/1.04  --splitting_grd                         true
% 3.03/1.04  --splitting_cvd                         false
% 3.03/1.04  --splitting_cvd_svl                     false
% 3.03/1.04  --splitting_nvd                         32
% 3.03/1.04  --sub_typing                            true
% 3.03/1.04  --prep_gs_sim                           true
% 3.03/1.04  --prep_unflatten                        true
% 3.03/1.04  --prep_res_sim                          true
% 3.03/1.04  --prep_upred                            true
% 3.03/1.04  --prep_sem_filter                       exhaustive
% 3.03/1.04  --prep_sem_filter_out                   false
% 3.03/1.04  --pred_elim                             true
% 3.03/1.04  --res_sim_input                         true
% 3.03/1.04  --eq_ax_congr_red                       true
% 3.03/1.04  --pure_diseq_elim                       true
% 3.03/1.04  --brand_transform                       false
% 3.03/1.04  --non_eq_to_eq                          false
% 3.03/1.04  --prep_def_merge                        true
% 3.03/1.04  --prep_def_merge_prop_impl              false
% 3.03/1.04  --prep_def_merge_mbd                    true
% 3.03/1.04  --prep_def_merge_tr_red                 false
% 3.03/1.04  --prep_def_merge_tr_cl                  false
% 3.03/1.04  --smt_preprocessing                     true
% 3.03/1.04  --smt_ac_axioms                         fast
% 3.03/1.04  --preprocessed_out                      false
% 3.03/1.04  --preprocessed_stats                    false
% 3.03/1.04  
% 3.03/1.04  ------ Abstraction refinement Options
% 3.03/1.04  
% 3.03/1.04  --abstr_ref                             []
% 3.03/1.04  --abstr_ref_prep                        false
% 3.03/1.04  --abstr_ref_until_sat                   false
% 3.03/1.04  --abstr_ref_sig_restrict                funpre
% 3.03/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/1.04  --abstr_ref_under                       []
% 3.03/1.04  
% 3.03/1.04  ------ SAT Options
% 3.03/1.04  
% 3.03/1.04  --sat_mode                              false
% 3.03/1.04  --sat_fm_restart_options                ""
% 3.03/1.04  --sat_gr_def                            false
% 3.03/1.04  --sat_epr_types                         true
% 3.03/1.04  --sat_non_cyclic_types                  false
% 3.03/1.04  --sat_finite_models                     false
% 3.03/1.04  --sat_fm_lemmas                         false
% 3.03/1.04  --sat_fm_prep                           false
% 3.03/1.04  --sat_fm_uc_incr                        true
% 3.03/1.04  --sat_out_model                         small
% 3.03/1.04  --sat_out_clauses                       false
% 3.03/1.04  
% 3.03/1.04  ------ QBF Options
% 3.03/1.04  
% 3.03/1.04  --qbf_mode                              false
% 3.03/1.04  --qbf_elim_univ                         false
% 3.03/1.04  --qbf_dom_inst                          none
% 3.03/1.04  --qbf_dom_pre_inst                      false
% 3.03/1.04  --qbf_sk_in                             false
% 3.03/1.04  --qbf_pred_elim                         true
% 3.03/1.04  --qbf_split                             512
% 3.03/1.04  
% 3.03/1.04  ------ BMC1 Options
% 3.03/1.04  
% 3.03/1.04  --bmc1_incremental                      false
% 3.03/1.04  --bmc1_axioms                           reachable_all
% 3.03/1.04  --bmc1_min_bound                        0
% 3.03/1.04  --bmc1_max_bound                        -1
% 3.03/1.04  --bmc1_max_bound_default                -1
% 3.03/1.04  --bmc1_symbol_reachability              true
% 3.03/1.04  --bmc1_property_lemmas                  false
% 3.03/1.04  --bmc1_k_induction                      false
% 3.03/1.04  --bmc1_non_equiv_states                 false
% 3.03/1.04  --bmc1_deadlock                         false
% 3.03/1.04  --bmc1_ucm                              false
% 3.03/1.04  --bmc1_add_unsat_core                   none
% 3.03/1.04  --bmc1_unsat_core_children              false
% 3.03/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/1.04  --bmc1_out_stat                         full
% 3.03/1.04  --bmc1_ground_init                      false
% 3.03/1.04  --bmc1_pre_inst_next_state              false
% 3.03/1.04  --bmc1_pre_inst_state                   false
% 3.03/1.04  --bmc1_pre_inst_reach_state             false
% 3.03/1.04  --bmc1_out_unsat_core                   false
% 3.03/1.04  --bmc1_aig_witness_out                  false
% 3.03/1.04  --bmc1_verbose                          false
% 3.03/1.04  --bmc1_dump_clauses_tptp                false
% 3.03/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.03/1.04  --bmc1_dump_file                        -
% 3.03/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.03/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.03/1.04  --bmc1_ucm_extend_mode                  1
% 3.03/1.04  --bmc1_ucm_init_mode                    2
% 3.03/1.04  --bmc1_ucm_cone_mode                    none
% 3.03/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.03/1.04  --bmc1_ucm_relax_model                  4
% 3.03/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.03/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/1.04  --bmc1_ucm_layered_model                none
% 3.03/1.04  --bmc1_ucm_max_lemma_size               10
% 3.03/1.04  
% 3.03/1.04  ------ AIG Options
% 3.03/1.04  
% 3.03/1.04  --aig_mode                              false
% 3.03/1.04  
% 3.03/1.04  ------ Instantiation Options
% 3.03/1.04  
% 3.03/1.04  --instantiation_flag                    true
% 3.03/1.04  --inst_sos_flag                         false
% 3.03/1.04  --inst_sos_phase                        true
% 3.03/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/1.04  --inst_lit_sel_side                     none
% 3.03/1.04  --inst_solver_per_active                1400
% 3.03/1.04  --inst_solver_calls_frac                1.
% 3.03/1.04  --inst_passive_queue_type               priority_queues
% 3.03/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/1.04  --inst_passive_queues_freq              [25;2]
% 3.03/1.04  --inst_dismatching                      true
% 3.03/1.04  --inst_eager_unprocessed_to_passive     true
% 3.03/1.04  --inst_prop_sim_given                   true
% 3.03/1.04  --inst_prop_sim_new                     false
% 3.03/1.04  --inst_subs_new                         false
% 3.03/1.04  --inst_eq_res_simp                      false
% 3.03/1.04  --inst_subs_given                       false
% 3.03/1.04  --inst_orphan_elimination               true
% 3.03/1.04  --inst_learning_loop_flag               true
% 3.03/1.04  --inst_learning_start                   3000
% 3.03/1.04  --inst_learning_factor                  2
% 3.03/1.04  --inst_start_prop_sim_after_learn       3
% 3.03/1.04  --inst_sel_renew                        solver
% 3.03/1.04  --inst_lit_activity_flag                true
% 3.03/1.04  --inst_restr_to_given                   false
% 3.03/1.04  --inst_activity_threshold               500
% 3.03/1.04  --inst_out_proof                        true
% 3.03/1.04  
% 3.03/1.04  ------ Resolution Options
% 3.03/1.04  
% 3.03/1.04  --resolution_flag                       false
% 3.03/1.04  --res_lit_sel                           adaptive
% 3.03/1.04  --res_lit_sel_side                      none
% 3.03/1.04  --res_ordering                          kbo
% 3.03/1.04  --res_to_prop_solver                    active
% 3.03/1.04  --res_prop_simpl_new                    false
% 3.03/1.04  --res_prop_simpl_given                  true
% 3.03/1.04  --res_passive_queue_type                priority_queues
% 3.03/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/1.04  --res_passive_queues_freq               [15;5]
% 3.03/1.04  --res_forward_subs                      full
% 3.03/1.04  --res_backward_subs                     full
% 3.03/1.04  --res_forward_subs_resolution           true
% 3.03/1.04  --res_backward_subs_resolution          true
% 3.03/1.04  --res_orphan_elimination                true
% 3.03/1.04  --res_time_limit                        2.
% 3.03/1.04  --res_out_proof                         true
% 3.03/1.04  
% 3.03/1.04  ------ Superposition Options
% 3.03/1.04  
% 3.03/1.04  --superposition_flag                    true
% 3.03/1.04  --sup_passive_queue_type                priority_queues
% 3.03/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.03/1.04  --demod_completeness_check              fast
% 3.03/1.04  --demod_use_ground                      true
% 3.03/1.04  --sup_to_prop_solver                    passive
% 3.03/1.04  --sup_prop_simpl_new                    true
% 3.03/1.04  --sup_prop_simpl_given                  true
% 3.03/1.04  --sup_fun_splitting                     false
% 3.03/1.04  --sup_smt_interval                      50000
% 3.03/1.04  
% 3.03/1.04  ------ Superposition Simplification Setup
% 3.03/1.04  
% 3.03/1.04  --sup_indices_passive                   []
% 3.03/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.04  --sup_full_bw                           [BwDemod]
% 3.03/1.04  --sup_immed_triv                        [TrivRules]
% 3.03/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.04  --sup_immed_bw_main                     []
% 3.03/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.04  
% 3.03/1.04  ------ Combination Options
% 3.03/1.04  
% 3.03/1.04  --comb_res_mult                         3
% 3.03/1.04  --comb_sup_mult                         2
% 3.03/1.04  --comb_inst_mult                        10
% 3.03/1.04  
% 3.03/1.04  ------ Debug Options
% 3.03/1.04  
% 3.03/1.04  --dbg_backtrace                         false
% 3.03/1.04  --dbg_dump_prop_clauses                 false
% 3.03/1.04  --dbg_dump_prop_clauses_file            -
% 3.03/1.04  --dbg_out_stat                          false
% 3.03/1.04  
% 3.03/1.04  
% 3.03/1.04  
% 3.03/1.04  
% 3.03/1.04  ------ Proving...
% 3.03/1.04  
% 3.03/1.04  
% 3.03/1.04  % SZS status Theorem for theBenchmark.p
% 3.03/1.04  
% 3.03/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.03/1.04  
% 3.03/1.04  fof(f7,axiom,(
% 3.03/1.04    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f68,plain,(
% 3.03/1.04    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.03/1.04    inference(cnf_transformation,[],[f7])).
% 3.03/1.04  
% 3.03/1.04  fof(f6,axiom,(
% 3.03/1.04    ! [X0] : k2_subset_1(X0) = X0),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f67,plain,(
% 3.03/1.04    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.03/1.04    inference(cnf_transformation,[],[f6])).
% 3.03/1.04  
% 3.03/1.04  fof(f22,conjecture,(
% 3.03/1.04    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f23,negated_conjecture,(
% 3.03/1.04    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 3.03/1.04    inference(negated_conjecture,[],[f22])).
% 3.03/1.04  
% 3.03/1.04  fof(f49,plain,(
% 3.03/1.04    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.03/1.04    inference(ennf_transformation,[],[f23])).
% 3.03/1.04  
% 3.03/1.04  fof(f50,plain,(
% 3.03/1.04    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.03/1.04    inference(flattening,[],[f49])).
% 3.03/1.04  
% 3.03/1.04  fof(f57,plain,(
% 3.03/1.04    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.03/1.04    introduced(choice_axiom,[])).
% 3.03/1.04  
% 3.03/1.04  fof(f56,plain,(
% 3.03/1.04    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.03/1.04    introduced(choice_axiom,[])).
% 3.03/1.04  
% 3.03/1.04  fof(f58,plain,(
% 3.03/1.04    (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.03/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f57,f56])).
% 3.03/1.04  
% 3.03/1.04  fof(f89,plain,(
% 3.03/1.04    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.03/1.04    inference(cnf_transformation,[],[f58])).
% 3.03/1.04  
% 3.03/1.04  fof(f15,axiom,(
% 3.03/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f37,plain,(
% 3.03/1.04    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.03/1.04    inference(ennf_transformation,[],[f15])).
% 3.03/1.04  
% 3.03/1.04  fof(f75,plain,(
% 3.03/1.04    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.03/1.04    inference(cnf_transformation,[],[f37])).
% 3.03/1.04  
% 3.03/1.04  fof(f88,plain,(
% 3.03/1.04    l1_pre_topc(sK0)),
% 3.03/1.04    inference(cnf_transformation,[],[f58])).
% 3.03/1.04  
% 3.03/1.04  fof(f19,axiom,(
% 3.03/1.04    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f43,plain,(
% 3.03/1.04    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.03/1.04    inference(ennf_transformation,[],[f19])).
% 3.03/1.04  
% 3.03/1.04  fof(f44,plain,(
% 3.03/1.04    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.03/1.04    inference(flattening,[],[f43])).
% 3.03/1.04  
% 3.03/1.04  fof(f54,plain,(
% 3.03/1.04    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.03/1.04    inference(nnf_transformation,[],[f44])).
% 3.03/1.04  
% 3.03/1.04  fof(f80,plain,(
% 3.03/1.04    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.03/1.04    inference(cnf_transformation,[],[f54])).
% 3.03/1.04  
% 3.03/1.04  fof(f95,plain,(
% 3.03/1.04    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.03/1.04    inference(equality_resolution,[],[f80])).
% 3.03/1.04  
% 3.03/1.04  fof(f16,axiom,(
% 3.03/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f38,plain,(
% 3.03/1.04    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.03/1.04    inference(ennf_transformation,[],[f16])).
% 3.03/1.04  
% 3.03/1.04  fof(f76,plain,(
% 3.03/1.04    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.03/1.04    inference(cnf_transformation,[],[f38])).
% 3.03/1.04  
% 3.03/1.04  fof(f85,plain,(
% 3.03/1.04    ~v2_struct_0(sK0)),
% 3.03/1.04    inference(cnf_transformation,[],[f58])).
% 3.03/1.04  
% 3.03/1.04  fof(f90,plain,(
% 3.03/1.04    ~v2_tex_2(sK1,sK0)),
% 3.03/1.04    inference(cnf_transformation,[],[f58])).
% 3.03/1.04  
% 3.03/1.04  fof(f11,axiom,(
% 3.03/1.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f26,plain,(
% 3.03/1.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 3.03/1.04    inference(pure_predicate_removal,[],[f11])).
% 3.03/1.04  
% 3.03/1.04  fof(f31,plain,(
% 3.03/1.04    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.03/1.04    inference(ennf_transformation,[],[f26])).
% 3.03/1.04  
% 3.03/1.04  fof(f32,plain,(
% 3.03/1.04    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.03/1.04    inference(flattening,[],[f31])).
% 3.03/1.04  
% 3.03/1.04  fof(f71,plain,(
% 3.03/1.04    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.03/1.04    inference(cnf_transformation,[],[f32])).
% 3.03/1.04  
% 3.03/1.04  fof(f18,axiom,(
% 3.03/1.04    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f24,plain,(
% 3.03/1.04    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 3.03/1.04    inference(pure_predicate_removal,[],[f18])).
% 3.03/1.04  
% 3.03/1.04  fof(f25,plain,(
% 3.03/1.04    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v1_tdlat_3(X1)))),
% 3.03/1.04    inference(pure_predicate_removal,[],[f24])).
% 3.03/1.04  
% 3.03/1.04  fof(f41,plain,(
% 3.03/1.04    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.03/1.04    inference(ennf_transformation,[],[f25])).
% 3.03/1.04  
% 3.03/1.04  fof(f42,plain,(
% 3.03/1.04    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.03/1.04    inference(flattening,[],[f41])).
% 3.03/1.04  
% 3.03/1.04  fof(f78,plain,(
% 3.03/1.04    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.03/1.04    inference(cnf_transformation,[],[f42])).
% 3.03/1.04  
% 3.03/1.04  fof(f86,plain,(
% 3.03/1.04    v2_pre_topc(sK0)),
% 3.03/1.04    inference(cnf_transformation,[],[f58])).
% 3.03/1.04  
% 3.03/1.04  fof(f87,plain,(
% 3.03/1.04    v1_tdlat_3(sK0)),
% 3.03/1.04    inference(cnf_transformation,[],[f58])).
% 3.03/1.04  
% 3.03/1.04  fof(f12,axiom,(
% 3.03/1.04    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f33,plain,(
% 3.03/1.04    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.03/1.04    inference(ennf_transformation,[],[f12])).
% 3.03/1.04  
% 3.03/1.04  fof(f72,plain,(
% 3.03/1.04    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.03/1.04    inference(cnf_transformation,[],[f33])).
% 3.03/1.04  
% 3.03/1.04  fof(f1,axiom,(
% 3.03/1.04    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f28,plain,(
% 3.03/1.04    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.03/1.04    inference(ennf_transformation,[],[f1])).
% 3.03/1.04  
% 3.03/1.04  fof(f59,plain,(
% 3.03/1.04    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.03/1.04    inference(cnf_transformation,[],[f28])).
% 3.03/1.04  
% 3.03/1.04  fof(f14,axiom,(
% 3.03/1.04    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f35,plain,(
% 3.03/1.04    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 3.03/1.04    inference(ennf_transformation,[],[f14])).
% 3.03/1.04  
% 3.03/1.04  fof(f36,plain,(
% 3.03/1.04    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 3.03/1.04    inference(flattening,[],[f35])).
% 3.03/1.04  
% 3.03/1.04  fof(f74,plain,(
% 3.03/1.04    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 3.03/1.04    inference(cnf_transformation,[],[f36])).
% 3.03/1.04  
% 3.03/1.04  fof(f13,axiom,(
% 3.03/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f34,plain,(
% 3.03/1.04    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.03/1.04    inference(ennf_transformation,[],[f13])).
% 3.03/1.04  
% 3.03/1.04  fof(f73,plain,(
% 3.03/1.04    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.03/1.04    inference(cnf_transformation,[],[f34])).
% 3.03/1.04  
% 3.03/1.04  fof(f8,axiom,(
% 3.03/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f30,plain,(
% 3.03/1.04    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.03/1.04    inference(ennf_transformation,[],[f8])).
% 3.03/1.04  
% 3.03/1.04  fof(f69,plain,(
% 3.03/1.04    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.03/1.04    inference(cnf_transformation,[],[f30])).
% 3.03/1.04  
% 3.03/1.04  fof(f5,axiom,(
% 3.03/1.04    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f66,plain,(
% 3.03/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.03/1.04    inference(cnf_transformation,[],[f5])).
% 3.03/1.04  
% 3.03/1.04  fof(f92,plain,(
% 3.03/1.04    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.03/1.04    inference(definition_unfolding,[],[f69,f66])).
% 3.03/1.04  
% 3.03/1.04  fof(f21,axiom,(
% 3.03/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f47,plain,(
% 3.03/1.04    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v2_tex_2(X2,X0) & ~v2_tex_2(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.03/1.04    inference(ennf_transformation,[],[f21])).
% 3.03/1.04  
% 3.03/1.04  fof(f48,plain,(
% 3.03/1.04    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v2_tex_2(X2,X0) & ~v2_tex_2(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.03/1.04    inference(flattening,[],[f47])).
% 3.03/1.04  
% 3.03/1.04  fof(f83,plain,(
% 3.03/1.04    ( ! [X2,X0,X1] : (v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.03/1.04    inference(cnf_transformation,[],[f48])).
% 3.03/1.04  
% 3.03/1.04  fof(f2,axiom,(
% 3.03/1.04    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f51,plain,(
% 3.03/1.04    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.03/1.04    inference(nnf_transformation,[],[f2])).
% 3.03/1.04  
% 3.03/1.04  fof(f52,plain,(
% 3.03/1.04    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.03/1.04    inference(flattening,[],[f51])).
% 3.03/1.04  
% 3.03/1.04  fof(f60,plain,(
% 3.03/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.03/1.04    inference(cnf_transformation,[],[f52])).
% 3.03/1.04  
% 3.03/1.04  fof(f94,plain,(
% 3.03/1.04    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.03/1.04    inference(equality_resolution,[],[f60])).
% 3.03/1.04  
% 3.03/1.04  fof(f3,axiom,(
% 3.03/1.04    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f53,plain,(
% 3.03/1.04    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 3.03/1.04    inference(nnf_transformation,[],[f3])).
% 3.03/1.04  
% 3.03/1.04  fof(f64,plain,(
% 3.03/1.04    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.03/1.04    inference(cnf_transformation,[],[f53])).
% 3.03/1.04  
% 3.03/1.04  fof(f4,axiom,(
% 3.03/1.04    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f29,plain,(
% 3.03/1.04    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.03/1.04    inference(ennf_transformation,[],[f4])).
% 3.03/1.04  
% 3.03/1.04  fof(f65,plain,(
% 3.03/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.03/1.04    inference(cnf_transformation,[],[f29])).
% 3.03/1.04  
% 3.03/1.04  fof(f91,plain,(
% 3.03/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.03/1.04    inference(definition_unfolding,[],[f65,f66])).
% 3.03/1.04  
% 3.03/1.04  fof(f20,axiom,(
% 3.03/1.04    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X0) = X1 => (v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)))))),
% 3.03/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.04  
% 3.03/1.04  fof(f45,plain,(
% 3.03/1.04    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.03/1.04    inference(ennf_transformation,[],[f20])).
% 3.03/1.04  
% 3.03/1.04  fof(f46,plain,(
% 3.03/1.04    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.03/1.04    inference(flattening,[],[f45])).
% 3.03/1.04  
% 3.03/1.04  fof(f55,plain,(
% 3.03/1.04    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_tdlat_3(X0)) & (v1_tdlat_3(X0) | ~v2_tex_2(X1,X0))) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.03/1.04    inference(nnf_transformation,[],[f46])).
% 3.03/1.04  
% 3.03/1.04  fof(f82,plain,(
% 3.03/1.04    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_tdlat_3(X0) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.03/1.04    inference(cnf_transformation,[],[f55])).
% 3.03/1.04  
% 3.03/1.04  fof(f97,plain,(
% 3.03/1.04    ( ! [X0] : (v2_tex_2(u1_struct_0(X0),X0) | ~v1_tdlat_3(X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.03/1.04    inference(equality_resolution,[],[f82])).
% 3.03/1.04  
% 3.03/1.04  cnf(c_8,plain,
% 3.03/1.04      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.03/1.04      inference(cnf_transformation,[],[f68]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_1586,plain,
% 3.03/1.04      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_7,plain,
% 3.03/1.04      ( k2_subset_1(X0) = X0 ),
% 3.03/1.04      inference(cnf_transformation,[],[f67]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_1608,plain,
% 3.03/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.03/1.04      inference(light_normalisation,[status(thm)],[c_1586,c_7]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_26,negated_conjecture,
% 3.03/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.03/1.04      inference(cnf_transformation,[],[f89]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_1574,plain,
% 3.03/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_15,plain,
% 3.03/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/1.04      | ~ l1_pre_topc(X1)
% 3.03/1.04      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 3.03/1.04      inference(cnf_transformation,[],[f75]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_1581,plain,
% 3.03/1.04      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
% 3.03/1.04      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.03/1.04      | l1_pre_topc(X0) != iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_2926,plain,
% 3.03/1.04      ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
% 3.03/1.04      | l1_pre_topc(sK0) != iProver_top ),
% 3.03/1.04      inference(superposition,[status(thm)],[c_1574,c_1581]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_27,negated_conjecture,
% 3.03/1.04      ( l1_pre_topc(sK0) ),
% 3.03/1.04      inference(cnf_transformation,[],[f88]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_1834,plain,
% 3.03/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.03/1.04      | ~ l1_pre_topc(sK0)
% 3.03/1.04      | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
% 3.03/1.04      inference(instantiation,[status(thm)],[c_15]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_3207,plain,
% 3.03/1.04      ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
% 3.03/1.04      inference(global_propositional_subsumption,
% 3.03/1.04                [status(thm)],
% 3.03/1.04                [c_2926,c_27,c_26,c_1834]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_19,plain,
% 3.03/1.04      ( v2_tex_2(u1_struct_0(X0),X1)
% 3.03/1.04      | ~ m1_pre_topc(X0,X1)
% 3.03/1.04      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/1.04      | ~ v1_tdlat_3(X0)
% 3.03/1.04      | v2_struct_0(X1)
% 3.03/1.04      | v2_struct_0(X0)
% 3.03/1.04      | ~ l1_pre_topc(X1) ),
% 3.03/1.04      inference(cnf_transformation,[],[f95]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_16,plain,
% 3.03/1.04      ( ~ m1_pre_topc(X0,X1)
% 3.03/1.04      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/1.04      | ~ l1_pre_topc(X1) ),
% 3.03/1.04      inference(cnf_transformation,[],[f76]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_168,plain,
% 3.03/1.04      ( ~ m1_pre_topc(X0,X1)
% 3.03/1.04      | v2_tex_2(u1_struct_0(X0),X1)
% 3.03/1.04      | ~ v1_tdlat_3(X0)
% 3.03/1.04      | v2_struct_0(X1)
% 3.03/1.04      | v2_struct_0(X0)
% 3.03/1.04      | ~ l1_pre_topc(X1) ),
% 3.03/1.04      inference(global_propositional_subsumption,
% 3.03/1.04                [status(thm)],
% 3.03/1.04                [c_19,c_16]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_169,plain,
% 3.03/1.04      ( v2_tex_2(u1_struct_0(X0),X1)
% 3.03/1.04      | ~ m1_pre_topc(X0,X1)
% 3.03/1.04      | ~ v1_tdlat_3(X0)
% 3.03/1.04      | v2_struct_0(X0)
% 3.03/1.04      | v2_struct_0(X1)
% 3.03/1.04      | ~ l1_pre_topc(X1) ),
% 3.03/1.04      inference(renaming,[status(thm)],[c_168]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_1569,plain,
% 3.03/1.04      ( v2_tex_2(u1_struct_0(X0),X1) = iProver_top
% 3.03/1.04      | m1_pre_topc(X0,X1) != iProver_top
% 3.03/1.04      | v1_tdlat_3(X0) != iProver_top
% 3.03/1.04      | v2_struct_0(X0) = iProver_top
% 3.03/1.04      | v2_struct_0(X1) = iProver_top
% 3.03/1.04      | l1_pre_topc(X1) != iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_169]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_3213,plain,
% 3.03/1.04      ( v2_tex_2(sK1,X0) = iProver_top
% 3.03/1.04      | m1_pre_topc(k1_pre_topc(sK0,sK1),X0) != iProver_top
% 3.03/1.04      | v1_tdlat_3(k1_pre_topc(sK0,sK1)) != iProver_top
% 3.03/1.04      | v2_struct_0(X0) = iProver_top
% 3.03/1.04      | v2_struct_0(k1_pre_topc(sK0,sK1)) = iProver_top
% 3.03/1.04      | l1_pre_topc(X0) != iProver_top ),
% 3.03/1.04      inference(superposition,[status(thm)],[c_3207,c_1569]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_30,negated_conjecture,
% 3.03/1.04      ( ~ v2_struct_0(sK0) ),
% 3.03/1.04      inference(cnf_transformation,[],[f85]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_31,plain,
% 3.03/1.04      ( v2_struct_0(sK0) != iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_34,plain,
% 3.03/1.04      ( l1_pre_topc(sK0) = iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_35,plain,
% 3.03/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_25,negated_conjecture,
% 3.03/1.04      ( ~ v2_tex_2(sK1,sK0) ),
% 3.03/1.04      inference(cnf_transformation,[],[f90]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_36,plain,
% 3.03/1.04      ( v2_tex_2(sK1,sK0) != iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_11,plain,
% 3.03/1.04      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 3.03/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.03/1.04      | ~ l1_pre_topc(X0) ),
% 3.03/1.04      inference(cnf_transformation,[],[f71]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_1827,plain,
% 3.03/1.04      ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
% 3.03/1.04      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.03/1.04      | ~ l1_pre_topc(sK0) ),
% 3.03/1.04      inference(instantiation,[status(thm)],[c_11]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_1828,plain,
% 3.03/1.04      ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top
% 3.03/1.04      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.03/1.04      | l1_pre_topc(sK0) != iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_1827]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_3259,plain,
% 3.03/1.04      ( v2_tex_2(sK1,sK0) = iProver_top
% 3.03/1.04      | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) != iProver_top
% 3.03/1.04      | v1_tdlat_3(k1_pre_topc(sK0,sK1)) != iProver_top
% 3.03/1.04      | v2_struct_0(k1_pre_topc(sK0,sK1)) = iProver_top
% 3.03/1.04      | v2_struct_0(sK0) = iProver_top
% 3.03/1.04      | l1_pre_topc(sK0) != iProver_top ),
% 3.03/1.04      inference(instantiation,[status(thm)],[c_3213]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_1583,plain,
% 3.03/1.04      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 3.03/1.04      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.03/1.04      | l1_pre_topc(X0) != iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_3068,plain,
% 3.03/1.04      ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top
% 3.03/1.04      | l1_pre_topc(sK0) != iProver_top ),
% 3.03/1.04      inference(superposition,[status(thm)],[c_1574,c_1583]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_3265,plain,
% 3.03/1.04      ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top ),
% 3.03/1.04      inference(global_propositional_subsumption,
% 3.03/1.04                [status(thm)],
% 3.03/1.04                [c_3068,c_34,c_35,c_1828]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_18,plain,
% 3.03/1.04      ( ~ m1_pre_topc(X0,X1)
% 3.03/1.04      | ~ v1_tdlat_3(X1)
% 3.03/1.04      | v1_tdlat_3(X0)
% 3.03/1.04      | ~ v2_pre_topc(X1)
% 3.03/1.04      | v2_struct_0(X1)
% 3.03/1.04      | ~ l1_pre_topc(X1) ),
% 3.03/1.04      inference(cnf_transformation,[],[f78]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_29,negated_conjecture,
% 3.03/1.04      ( v2_pre_topc(sK0) ),
% 3.03/1.04      inference(cnf_transformation,[],[f86]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_437,plain,
% 3.03/1.04      ( ~ m1_pre_topc(X0,X1)
% 3.03/1.04      | ~ v1_tdlat_3(X1)
% 3.03/1.04      | v1_tdlat_3(X0)
% 3.03/1.04      | v2_struct_0(X1)
% 3.03/1.04      | ~ l1_pre_topc(X1)
% 3.03/1.04      | sK0 != X1 ),
% 3.03/1.04      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_438,plain,
% 3.03/1.04      ( ~ m1_pre_topc(X0,sK0)
% 3.03/1.04      | v1_tdlat_3(X0)
% 3.03/1.04      | ~ v1_tdlat_3(sK0)
% 3.03/1.04      | v2_struct_0(sK0)
% 3.03/1.04      | ~ l1_pre_topc(sK0) ),
% 3.03/1.04      inference(unflattening,[status(thm)],[c_437]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_28,negated_conjecture,
% 3.03/1.04      ( v1_tdlat_3(sK0) ),
% 3.03/1.04      inference(cnf_transformation,[],[f87]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_440,plain,
% 3.03/1.04      ( v1_tdlat_3(X0) | ~ m1_pre_topc(X0,sK0) ),
% 3.03/1.04      inference(global_propositional_subsumption,
% 3.03/1.04                [status(thm)],
% 3.03/1.04                [c_438,c_30,c_28,c_27]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_441,plain,
% 3.03/1.04      ( ~ m1_pre_topc(X0,sK0) | v1_tdlat_3(X0) ),
% 3.03/1.04      inference(renaming,[status(thm)],[c_440]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_1566,plain,
% 3.03/1.04      ( m1_pre_topc(X0,sK0) != iProver_top
% 3.03/1.04      | v1_tdlat_3(X0) = iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_3272,plain,
% 3.03/1.04      ( v1_tdlat_3(k1_pre_topc(sK0,sK1)) = iProver_top ),
% 3.03/1.04      inference(superposition,[status(thm)],[c_3265,c_1566]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_4403,plain,
% 3.03/1.04      ( v2_struct_0(k1_pre_topc(sK0,sK1)) = iProver_top ),
% 3.03/1.04      inference(global_propositional_subsumption,
% 3.03/1.04                [status(thm)],
% 3.03/1.04                [c_3213,c_31,c_34,c_35,c_36,c_1828,c_3259,c_3272]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_12,plain,
% 3.03/1.04      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.03/1.04      inference(cnf_transformation,[],[f72]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_0,plain,
% 3.03/1.04      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.03/1.04      inference(cnf_transformation,[],[f59]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_14,plain,
% 3.03/1.04      ( ~ v2_struct_0(X0)
% 3.03/1.04      | ~ l1_struct_0(X0)
% 3.03/1.04      | v1_xboole_0(u1_struct_0(X0)) ),
% 3.03/1.04      inference(cnf_transformation,[],[f74]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_385,plain,
% 3.03/1.04      ( ~ v2_struct_0(X0)
% 3.03/1.04      | ~ l1_struct_0(X0)
% 3.03/1.04      | u1_struct_0(X0) != X1
% 3.03/1.04      | k1_xboole_0 = X1 ),
% 3.03/1.04      inference(resolution_lifted,[status(thm)],[c_0,c_14]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_386,plain,
% 3.03/1.04      ( ~ v2_struct_0(X0)
% 3.03/1.04      | ~ l1_struct_0(X0)
% 3.03/1.04      | k1_xboole_0 = u1_struct_0(X0) ),
% 3.03/1.04      inference(unflattening,[status(thm)],[c_385]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_402,plain,
% 3.03/1.04      ( ~ v2_struct_0(X0)
% 3.03/1.04      | ~ l1_pre_topc(X0)
% 3.03/1.04      | u1_struct_0(X0) = k1_xboole_0 ),
% 3.03/1.04      inference(resolution,[status(thm)],[c_12,c_386]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_1568,plain,
% 3.03/1.04      ( u1_struct_0(X0) = k1_xboole_0
% 3.03/1.04      | v2_struct_0(X0) != iProver_top
% 3.03/1.04      | l1_pre_topc(X0) != iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_4408,plain,
% 3.03/1.04      ( u1_struct_0(k1_pre_topc(sK0,sK1)) = k1_xboole_0
% 3.03/1.04      | l1_pre_topc(k1_pre_topc(sK0,sK1)) != iProver_top ),
% 3.03/1.04      inference(superposition,[status(thm)],[c_4403,c_1568]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_4409,plain,
% 3.03/1.04      ( sK1 = k1_xboole_0
% 3.03/1.04      | l1_pre_topc(k1_pre_topc(sK0,sK1)) != iProver_top ),
% 3.03/1.04      inference(demodulation,[status(thm)],[c_4408,c_3207]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_13,plain,
% 3.03/1.04      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.03/1.04      inference(cnf_transformation,[],[f73]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_1582,plain,
% 3.03/1.04      ( m1_pre_topc(X0,X1) != iProver_top
% 3.03/1.04      | l1_pre_topc(X1) != iProver_top
% 3.03/1.04      | l1_pre_topc(X0) = iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_3270,plain,
% 3.03/1.04      ( l1_pre_topc(k1_pre_topc(sK0,sK1)) = iProver_top
% 3.03/1.04      | l1_pre_topc(sK0) != iProver_top ),
% 3.03/1.04      inference(superposition,[status(thm)],[c_3265,c_1582]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_4412,plain,
% 3.03/1.04      ( sK1 = k1_xboole_0 ),
% 3.03/1.04      inference(global_propositional_subsumption,
% 3.03/1.04                [status(thm)],
% 3.03/1.04                [c_4409,c_34,c_3270]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_9,plain,
% 3.03/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.03/1.04      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 3.03/1.04      inference(cnf_transformation,[],[f92]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_1585,plain,
% 3.03/1.04      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 3.03/1.04      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_2835,plain,
% 3.03/1.04      ( k4_xboole_0(X0,k4_xboole_0(X0,sK1)) = k9_subset_1(u1_struct_0(sK0),X0,sK1) ),
% 3.03/1.04      inference(superposition,[status(thm)],[c_1574,c_1585]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_24,plain,
% 3.03/1.04      ( ~ v2_tex_2(X0,X1)
% 3.03/1.04      | v2_tex_2(k9_subset_1(u1_struct_0(X1),X0,X2),X1)
% 3.03/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/1.04      | ~ l1_pre_topc(X1) ),
% 3.03/1.04      inference(cnf_transformation,[],[f83]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_1576,plain,
% 3.03/1.04      ( v2_tex_2(X0,X1) != iProver_top
% 3.03/1.04      | v2_tex_2(k9_subset_1(u1_struct_0(X1),X0,X2),X1) = iProver_top
% 3.03/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.03/1.04      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.03/1.04      | l1_pre_topc(X1) != iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_3808,plain,
% 3.03/1.04      ( v2_tex_2(X0,sK0) != iProver_top
% 3.03/1.04      | v2_tex_2(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),sK0) = iProver_top
% 3.03/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.03/1.04      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.03/1.04      | l1_pre_topc(sK0) != iProver_top ),
% 3.03/1.04      inference(superposition,[status(thm)],[c_2835,c_1576]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_4247,plain,
% 3.03/1.04      ( v2_tex_2(X0,sK0) != iProver_top
% 3.03/1.04      | v2_tex_2(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),sK0) = iProver_top
% 3.03/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.03/1.04      inference(global_propositional_subsumption,
% 3.03/1.04                [status(thm)],
% 3.03/1.04                [c_3808,c_34,c_35]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_4419,plain,
% 3.03/1.04      ( v2_tex_2(X0,sK0) != iProver_top
% 3.03/1.04      | v2_tex_2(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),sK0) = iProver_top
% 3.03/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.03/1.04      inference(demodulation,[status(thm)],[c_4412,c_4247]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_3,plain,
% 3.03/1.04      ( r1_tarski(X0,X0) ),
% 3.03/1.04      inference(cnf_transformation,[],[f94]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_1590,plain,
% 3.03/1.04      ( r1_tarski(X0,X0) = iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_4,plain,
% 3.03/1.04      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.03/1.04      inference(cnf_transformation,[],[f64]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_1589,plain,
% 3.03/1.04      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.03/1.04      | r1_tarski(X0,X1) != iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_2243,plain,
% 3.03/1.04      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.03/1.04      inference(superposition,[status(thm)],[c_1590,c_1589]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_6,plain,
% 3.03/1.04      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.03/1.04      inference(cnf_transformation,[],[f91]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_1587,plain,
% 3.03/1.04      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 3.03/1.04      | r1_tarski(X0,X1) != iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_2459,plain,
% 3.03/1.04      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.03/1.04      inference(superposition,[status(thm)],[c_1590,c_1587]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_2460,plain,
% 3.03/1.04      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.03/1.04      inference(light_normalisation,[status(thm)],[c_2459,c_2243]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_4472,plain,
% 3.03/1.04      ( v2_tex_2(X0,sK0) != iProver_top
% 3.03/1.04      | v2_tex_2(k1_xboole_0,sK0) = iProver_top
% 3.03/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.03/1.04      inference(light_normalisation,[status(thm)],[c_4419,c_2243,c_2460]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_1575,plain,
% 3.03/1.04      ( v2_tex_2(sK1,sK0) != iProver_top ),
% 3.03/1.04      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_4433,plain,
% 3.03/1.04      ( v2_tex_2(k1_xboole_0,sK0) != iProver_top ),
% 3.03/1.04      inference(demodulation,[status(thm)],[c_4412,c_1575]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_12082,plain,
% 3.03/1.04      ( v2_tex_2(X0,sK0) != iProver_top
% 3.03/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.03/1.04      inference(global_propositional_subsumption,
% 3.03/1.04                [status(thm)],
% 3.03/1.04                [c_4472,c_4433]) ).
% 3.03/1.04  
% 3.03/1.04  cnf(c_12092,plain,
% 3.03/1.04      ( v2_tex_2(u1_struct_0(sK0),sK0) != iProver_top ),
% 3.03/1.04      inference(superposition,[status(thm)],[c_1608,c_12082]) ).
% 3.03/1.05  
% 3.03/1.05  cnf(c_21,plain,
% 3.03/1.05      ( v2_tex_2(u1_struct_0(X0),X0)
% 3.03/1.05      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.03/1.05      | ~ v1_tdlat_3(X0)
% 3.03/1.05      | v2_struct_0(X0)
% 3.03/1.05      | ~ l1_pre_topc(X0) ),
% 3.03/1.05      inference(cnf_transformation,[],[f97]) ).
% 3.03/1.05  
% 3.03/1.05  cnf(c_1579,plain,
% 3.03/1.05      ( v2_tex_2(u1_struct_0(X0),X0) = iProver_top
% 3.03/1.05      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.03/1.05      | v1_tdlat_3(X0) != iProver_top
% 3.03/1.05      | v2_struct_0(X0) = iProver_top
% 3.03/1.05      | l1_pre_topc(X0) != iProver_top ),
% 3.03/1.05      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.03/1.05  
% 3.03/1.05  cnf(c_1692,plain,
% 3.03/1.05      ( v2_tex_2(u1_struct_0(X0),X0) = iProver_top
% 3.03/1.05      | v1_tdlat_3(X0) != iProver_top
% 3.03/1.05      | v2_struct_0(X0) = iProver_top
% 3.03/1.05      | l1_pre_topc(X0) != iProver_top ),
% 3.03/1.05      inference(forward_subsumption_resolution,
% 3.03/1.05                [status(thm)],
% 3.03/1.05                [c_1579,c_1608]) ).
% 3.03/1.05  
% 3.03/1.05  cnf(c_1765,plain,
% 3.03/1.05      ( v2_tex_2(u1_struct_0(sK0),sK0) = iProver_top
% 3.03/1.05      | v1_tdlat_3(sK0) != iProver_top
% 3.03/1.05      | v2_struct_0(sK0) = iProver_top
% 3.03/1.05      | l1_pre_topc(sK0) != iProver_top ),
% 3.03/1.05      inference(instantiation,[status(thm)],[c_1692]) ).
% 3.03/1.05  
% 3.03/1.05  cnf(c_33,plain,
% 3.03/1.05      ( v1_tdlat_3(sK0) = iProver_top ),
% 3.03/1.05      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.03/1.05  
% 3.03/1.05  cnf(contradiction,plain,
% 3.03/1.05      ( $false ),
% 3.03/1.05      inference(minisat,[status(thm)],[c_12092,c_1765,c_34,c_33,c_31]) ).
% 3.03/1.05  
% 3.03/1.05  
% 3.03/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 3.03/1.05  
% 3.03/1.05  ------                               Statistics
% 3.03/1.05  
% 3.03/1.05  ------ General
% 3.03/1.05  
% 3.03/1.05  abstr_ref_over_cycles:                  0
% 3.03/1.05  abstr_ref_under_cycles:                 0
% 3.03/1.05  gc_basic_clause_elim:                   0
% 3.03/1.05  forced_gc_time:                         0
% 3.03/1.05  parsing_time:                           0.009
% 3.03/1.05  unif_index_cands_time:                  0.
% 3.03/1.05  unif_index_add_time:                    0.
% 3.03/1.05  orderings_time:                         0.
% 3.03/1.05  out_proof_time:                         0.008
% 3.03/1.05  total_time:                             0.304
% 3.03/1.05  num_of_symbols:                         50
% 3.03/1.05  num_of_terms:                           11836
% 3.03/1.05  
% 3.03/1.05  ------ Preprocessing
% 3.03/1.05  
% 3.03/1.05  num_of_splits:                          0
% 3.03/1.05  num_of_split_atoms:                     0
% 3.03/1.05  num_of_reused_defs:                     0
% 3.03/1.05  num_eq_ax_congr_red:                    26
% 3.03/1.05  num_of_sem_filtered_clauses:            1
% 3.03/1.05  num_of_subtypes:                        0
% 3.03/1.05  monotx_restored_types:                  0
% 3.03/1.05  sat_num_of_epr_types:                   0
% 3.03/1.05  sat_num_of_non_cyclic_types:            0
% 3.03/1.05  sat_guarded_non_collapsed_types:        0
% 3.03/1.05  num_pure_diseq_elim:                    0
% 3.03/1.05  simp_replaced_by:                       0
% 3.03/1.05  res_preprocessed:                       136
% 3.03/1.05  prep_upred:                             0
% 3.03/1.05  prep_unflattend:                        27
% 3.03/1.05  smt_new_axioms:                         0
% 3.03/1.05  pred_elim_cands:                        7
% 3.03/1.05  pred_elim:                              3
% 3.03/1.05  pred_elim_cl:                           3
% 3.03/1.05  pred_elim_cycles:                       5
% 3.03/1.05  merged_defs:                            8
% 3.03/1.05  merged_defs_ncl:                        0
% 3.03/1.05  bin_hyper_res:                          8
% 3.03/1.05  prep_cycles:                            4
% 3.03/1.05  pred_elim_time:                         0.004
% 3.03/1.05  splitting_time:                         0.
% 3.03/1.05  sem_filter_time:                        0.
% 3.03/1.05  monotx_time:                            0.
% 3.03/1.05  subtype_inf_time:                       0.
% 3.03/1.05  
% 3.03/1.05  ------ Problem properties
% 3.03/1.05  
% 3.03/1.05  clauses:                                27
% 3.03/1.05  conjectures:                            5
% 3.03/1.05  epr:                                    9
% 3.03/1.05  horn:                                   22
% 3.03/1.05  ground:                                 5
% 3.03/1.05  unary:                                  9
% 3.03/1.05  binary:                                 5
% 3.03/1.05  lits:                                   74
% 3.03/1.05  lits_eq:                                8
% 3.03/1.05  fd_pure:                                0
% 3.03/1.05  fd_pseudo:                              0
% 3.03/1.05  fd_cond:                                0
% 3.03/1.05  fd_pseudo_cond:                         1
% 3.03/1.05  ac_symbols:                             0
% 3.03/1.05  
% 3.03/1.05  ------ Propositional Solver
% 3.03/1.05  
% 3.03/1.05  prop_solver_calls:                      27
% 3.03/1.05  prop_fast_solver_calls:                 1307
% 3.03/1.05  smt_solver_calls:                       0
% 3.03/1.05  smt_fast_solver_calls:                  0
% 3.03/1.05  prop_num_of_clauses:                    4407
% 3.03/1.05  prop_preprocess_simplified:             10276
% 3.03/1.05  prop_fo_subsumed:                       74
% 3.03/1.05  prop_solver_time:                       0.
% 3.03/1.05  smt_solver_time:                        0.
% 3.03/1.05  smt_fast_solver_time:                   0.
% 3.03/1.05  prop_fast_solver_time:                  0.
% 3.03/1.05  prop_unsat_core_time:                   0.
% 3.03/1.05  
% 3.03/1.05  ------ QBF
% 3.03/1.05  
% 3.03/1.05  qbf_q_res:                              0
% 3.03/1.05  qbf_num_tautologies:                    0
% 3.03/1.05  qbf_prep_cycles:                        0
% 3.03/1.05  
% 3.03/1.05  ------ BMC1
% 3.03/1.05  
% 3.03/1.05  bmc1_current_bound:                     -1
% 3.03/1.05  bmc1_last_solved_bound:                 -1
% 3.03/1.05  bmc1_unsat_core_size:                   -1
% 3.03/1.05  bmc1_unsat_core_parents_size:           -1
% 3.03/1.05  bmc1_merge_next_fun:                    0
% 3.03/1.05  bmc1_unsat_core_clauses_time:           0.
% 3.03/1.05  
% 3.03/1.05  ------ Instantiation
% 3.03/1.05  
% 3.03/1.05  inst_num_of_clauses:                    1260
% 3.03/1.05  inst_num_in_passive:                    98
% 3.03/1.05  inst_num_in_active:                     595
% 3.03/1.05  inst_num_in_unprocessed:                567
% 3.03/1.05  inst_num_of_loops:                      630
% 3.03/1.05  inst_num_of_learning_restarts:          0
% 3.03/1.05  inst_num_moves_active_passive:          31
% 3.03/1.05  inst_lit_activity:                      0
% 3.03/1.05  inst_lit_activity_moves:                0
% 3.03/1.05  inst_num_tautologies:                   0
% 3.03/1.05  inst_num_prop_implied:                  0
% 3.03/1.05  inst_num_existing_simplified:           0
% 3.03/1.05  inst_num_eq_res_simplified:             0
% 3.03/1.05  inst_num_child_elim:                    0
% 3.03/1.05  inst_num_of_dismatching_blockings:      860
% 3.03/1.05  inst_num_of_non_proper_insts:           1662
% 3.03/1.05  inst_num_of_duplicates:                 0
% 3.03/1.05  inst_inst_num_from_inst_to_res:         0
% 3.03/1.05  inst_dismatching_checking_time:         0.
% 3.03/1.05  
% 3.03/1.05  ------ Resolution
% 3.03/1.05  
% 3.03/1.05  res_num_of_clauses:                     0
% 3.03/1.05  res_num_in_passive:                     0
% 3.03/1.05  res_num_in_active:                      0
% 3.03/1.05  res_num_of_loops:                       140
% 3.03/1.05  res_forward_subset_subsumed:            89
% 3.03/1.05  res_backward_subset_subsumed:           4
% 3.03/1.05  res_forward_subsumed:                   0
% 3.03/1.05  res_backward_subsumed:                  0
% 3.03/1.05  res_forward_subsumption_resolution:     0
% 3.03/1.05  res_backward_subsumption_resolution:    0
% 3.03/1.05  res_clause_to_clause_subsumption:       785
% 3.03/1.05  res_orphan_elimination:                 0
% 3.03/1.05  res_tautology_del:                      100
% 3.03/1.05  res_num_eq_res_simplified:              0
% 3.03/1.05  res_num_sel_changes:                    0
% 3.03/1.05  res_moves_from_active_to_pass:          0
% 3.03/1.05  
% 3.03/1.05  ------ Superposition
% 3.03/1.05  
% 3.03/1.05  sup_time_total:                         0.
% 3.03/1.05  sup_time_generating:                    0.
% 3.03/1.05  sup_time_sim_full:                      0.
% 3.03/1.05  sup_time_sim_immed:                     0.
% 3.03/1.05  
% 3.03/1.05  sup_num_of_clauses:                     245
% 3.03/1.05  sup_num_in_active:                      107
% 3.03/1.05  sup_num_in_passive:                     138
% 3.03/1.05  sup_num_of_loops:                       125
% 3.03/1.05  sup_fw_superposition:                   174
% 3.03/1.05  sup_bw_superposition:                   220
% 3.03/1.05  sup_immediate_simplified:               166
% 3.03/1.05  sup_given_eliminated:                   0
% 3.03/1.05  comparisons_done:                       0
% 3.03/1.05  comparisons_avoided:                    0
% 3.03/1.05  
% 3.03/1.05  ------ Simplifications
% 3.03/1.05  
% 3.03/1.05  
% 3.03/1.05  sim_fw_subset_subsumed:                 53
% 3.03/1.05  sim_bw_subset_subsumed:                 3
% 3.03/1.05  sim_fw_subsumed:                        53
% 3.03/1.05  sim_bw_subsumed:                        0
% 3.03/1.05  sim_fw_subsumption_res:                 2
% 3.03/1.05  sim_bw_subsumption_res:                 0
% 3.03/1.05  sim_tautology_del:                      9
% 3.03/1.05  sim_eq_tautology_del:                   20
% 3.03/1.05  sim_eq_res_simp:                        1
% 3.03/1.05  sim_fw_demodulated:                     2
% 3.03/1.05  sim_bw_demodulated:                     19
% 3.03/1.05  sim_light_normalised:                   92
% 3.03/1.05  sim_joinable_taut:                      0
% 3.03/1.05  sim_joinable_simp:                      0
% 3.03/1.05  sim_ac_normalised:                      0
% 3.03/1.05  sim_smt_subsumption:                    0
% 3.03/1.05  
%------------------------------------------------------------------------------
