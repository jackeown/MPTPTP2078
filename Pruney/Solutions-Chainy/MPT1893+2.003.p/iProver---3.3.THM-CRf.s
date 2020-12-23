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
% DateTime   : Thu Dec  3 12:27:38 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 825 expanded)
%              Number of clauses        :   74 ( 202 expanded)
%              Number of leaves         :   20 ( 222 expanded)
%              Depth                    :   21
%              Number of atoms          :  493 (5703 expanded)
%              Number of equality atoms :   97 ( 194 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( v1_subset_1(X1,u1_struct_0(X0))
              & v3_tex_2(X1,X0)
              & ( v4_pre_topc(X1,X0)
                | v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( v1_subset_1(X1,u1_struct_0(X0))
                & v3_tex_2(X1,X0)
                & ( v4_pre_topc(X1,X0)
                  | v3_pre_topc(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_subset_1(sK2,u1_struct_0(X0))
        & v3_tex_2(sK2,X0)
        & ( v4_pre_topc(sK2,X0)
          | v3_pre_topc(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_subset_1(X1,u1_struct_0(X0))
            & v3_tex_2(X1,X0)
            & ( v4_pre_topc(X1,X0)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(sK1))
          & v3_tex_2(X1,sK1)
          & ( v4_pre_topc(X1,sK1)
            | v3_pre_topc(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v3_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( v1_subset_1(sK2,u1_struct_0(sK1))
    & v3_tex_2(sK2,sK1)
    & ( v4_pre_topc(sK2,sK1)
      | v3_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v3_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f35,f43,f42])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0),X0)
        & v4_pre_topc(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK0(X0),X0)
            & v4_pre_topc(sK0(X0),X0)
            & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f62,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,
    ( v4_pre_topc(sK2,sK1)
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f47,f50])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f45,f50,f50])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & v1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_841,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_489,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_490,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_838,plain,
    ( k2_pre_topc(sK1,X0) = X0
    | v4_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_490])).

cnf(c_1003,plain,
    ( k2_pre_topc(sK1,sK2) = sK2
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_841,c_838])).

cnf(c_14,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_22,negated_conjecture,
    ( v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_368,plain,
    ( v1_tops_1(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_22])).

cnf(c_369,plain,
    ( v1_tops_1(sK2,sK1)
    | ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_371,plain,
    ( v1_tops_1(sK2,sK1)
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_28,c_27,c_25,c_24])).

cnf(c_386,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_371])).

cnf(c_387,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_389,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_25,c_24])).

cnf(c_19,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_409,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_410,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_26,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_414,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_410,c_26,c_25])).

cnf(c_526,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_389,c_414])).

cnf(c_527,plain,
    ( ~ v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_23,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_516,plain,
    ( v4_pre_topc(sK2,sK1)
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_23,c_389])).

cnf(c_529,plain,
    ( k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_527,c_24,c_516])).

cnf(c_1004,plain,
    ( u1_struct_0(sK1) = sK2
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1003,c_529])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_11,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_474,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_475,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
    | v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_555,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | v4_pre_topc(X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),X1) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_414,c_475])).

cnf(c_556,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_568,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_556,c_6])).

cnf(c_925,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_568])).

cnf(c_926,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) != iProver_top
    | v4_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_925])).

cnf(c_931,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_932,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_931])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_937,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_534,plain,
    ( v4_pre_topc(X0,sK1)
    | v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),X0) != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_475])).

cnf(c_596,plain,
    ( v4_pre_topc(X0,sK1)
    | v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),X0) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_534])).

cnf(c_1020,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_596])).

cnf(c_1021,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) != sK2
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
    | v4_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1020])).

cnf(c_1044,plain,
    ( u1_struct_0(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1004,c_24,c_33,c_926,c_932,c_937,c_1021])).

cnf(c_1051,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1044,c_841])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_844,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1751,plain,
    ( k3_subset_1(sK2,sK2) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_1051,c_844])).

cnf(c_2,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_306,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2
    | k1_xboole_0 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_307,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1231,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_1820,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_307,c_1231])).

cnf(c_1942,plain,
    ( k3_subset_1(sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1751,c_1820])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_15,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_8,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_156,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_8])).

cnf(c_157,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
    inference(renaming,[status(thm)],[c_156])).

cnf(c_325,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_157])).

cnf(c_21,negated_conjecture,
    ( v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) != k1_xboole_0
    | u1_struct_0(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_325,c_21])).

cnf(c_347,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_349,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_347,c_24])).

cnf(c_1052,plain,
    ( k3_subset_1(sK2,sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1044,c_349])).

cnf(c_1944,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1942,c_1052])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:24:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.58/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/0.99  
% 2.58/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.58/0.99  
% 2.58/0.99  ------  iProver source info
% 2.58/0.99  
% 2.58/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.58/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.58/0.99  git: non_committed_changes: false
% 2.58/0.99  git: last_make_outside_of_git: false
% 2.58/0.99  
% 2.58/0.99  ------ 
% 2.58/0.99  
% 2.58/0.99  ------ Input Options
% 2.58/0.99  
% 2.58/0.99  --out_options                           all
% 2.58/0.99  --tptp_safe_out                         true
% 2.58/0.99  --problem_path                          ""
% 2.58/0.99  --include_path                          ""
% 2.58/0.99  --clausifier                            res/vclausify_rel
% 2.58/0.99  --clausifier_options                    --mode clausify
% 2.58/0.99  --stdin                                 false
% 2.58/0.99  --stats_out                             all
% 2.58/0.99  
% 2.58/0.99  ------ General Options
% 2.58/0.99  
% 2.58/0.99  --fof                                   false
% 2.58/0.99  --time_out_real                         305.
% 2.58/0.99  --time_out_virtual                      -1.
% 2.58/0.99  --symbol_type_check                     false
% 2.58/0.99  --clausify_out                          false
% 2.58/0.99  --sig_cnt_out                           false
% 2.58/0.99  --trig_cnt_out                          false
% 2.58/0.99  --trig_cnt_out_tolerance                1.
% 2.58/0.99  --trig_cnt_out_sk_spl                   false
% 2.58/0.99  --abstr_cl_out                          false
% 2.58/0.99  
% 2.58/0.99  ------ Global Options
% 2.58/0.99  
% 2.58/0.99  --schedule                              default
% 2.58/0.99  --add_important_lit                     false
% 2.58/0.99  --prop_solver_per_cl                    1000
% 2.58/0.99  --min_unsat_core                        false
% 2.58/0.99  --soft_assumptions                      false
% 2.58/0.99  --soft_lemma_size                       3
% 2.58/0.99  --prop_impl_unit_size                   0
% 2.58/0.99  --prop_impl_unit                        []
% 2.58/0.99  --share_sel_clauses                     true
% 2.58/0.99  --reset_solvers                         false
% 2.58/0.99  --bc_imp_inh                            [conj_cone]
% 2.58/0.99  --conj_cone_tolerance                   3.
% 2.58/0.99  --extra_neg_conj                        none
% 2.58/0.99  --large_theory_mode                     true
% 2.58/0.99  --prolific_symb_bound                   200
% 2.58/0.99  --lt_threshold                          2000
% 2.58/0.99  --clause_weak_htbl                      true
% 2.58/0.99  --gc_record_bc_elim                     false
% 2.58/0.99  
% 2.58/0.99  ------ Preprocessing Options
% 2.58/0.99  
% 2.58/0.99  --preprocessing_flag                    true
% 2.58/0.99  --time_out_prep_mult                    0.1
% 2.58/0.99  --splitting_mode                        input
% 2.58/0.99  --splitting_grd                         true
% 2.58/0.99  --splitting_cvd                         false
% 2.58/0.99  --splitting_cvd_svl                     false
% 2.58/0.99  --splitting_nvd                         32
% 2.58/0.99  --sub_typing                            true
% 2.58/0.99  --prep_gs_sim                           true
% 2.58/0.99  --prep_unflatten                        true
% 2.58/0.99  --prep_res_sim                          true
% 2.58/0.99  --prep_upred                            true
% 2.58/0.99  --prep_sem_filter                       exhaustive
% 2.58/0.99  --prep_sem_filter_out                   false
% 2.58/0.99  --pred_elim                             true
% 2.58/0.99  --res_sim_input                         true
% 2.58/0.99  --eq_ax_congr_red                       true
% 2.58/0.99  --pure_diseq_elim                       true
% 2.58/0.99  --brand_transform                       false
% 2.58/0.99  --non_eq_to_eq                          false
% 2.58/0.99  --prep_def_merge                        true
% 2.58/0.99  --prep_def_merge_prop_impl              false
% 2.58/0.99  --prep_def_merge_mbd                    true
% 2.58/0.99  --prep_def_merge_tr_red                 false
% 2.58/0.99  --prep_def_merge_tr_cl                  false
% 2.58/0.99  --smt_preprocessing                     true
% 2.58/0.99  --smt_ac_axioms                         fast
% 2.58/0.99  --preprocessed_out                      false
% 2.58/0.99  --preprocessed_stats                    false
% 2.58/0.99  
% 2.58/0.99  ------ Abstraction refinement Options
% 2.58/0.99  
% 2.58/0.99  --abstr_ref                             []
% 2.58/0.99  --abstr_ref_prep                        false
% 2.58/0.99  --abstr_ref_until_sat                   false
% 2.58/0.99  --abstr_ref_sig_restrict                funpre
% 2.58/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.58/0.99  --abstr_ref_under                       []
% 2.58/0.99  
% 2.58/0.99  ------ SAT Options
% 2.58/0.99  
% 2.58/0.99  --sat_mode                              false
% 2.58/0.99  --sat_fm_restart_options                ""
% 2.58/0.99  --sat_gr_def                            false
% 2.58/0.99  --sat_epr_types                         true
% 2.58/0.99  --sat_non_cyclic_types                  false
% 2.58/0.99  --sat_finite_models                     false
% 2.58/0.99  --sat_fm_lemmas                         false
% 2.58/0.99  --sat_fm_prep                           false
% 2.58/0.99  --sat_fm_uc_incr                        true
% 2.58/0.99  --sat_out_model                         small
% 2.58/0.99  --sat_out_clauses                       false
% 2.58/0.99  
% 2.58/0.99  ------ QBF Options
% 2.58/0.99  
% 2.58/0.99  --qbf_mode                              false
% 2.58/0.99  --qbf_elim_univ                         false
% 2.58/0.99  --qbf_dom_inst                          none
% 2.58/0.99  --qbf_dom_pre_inst                      false
% 2.58/0.99  --qbf_sk_in                             false
% 2.58/0.99  --qbf_pred_elim                         true
% 2.58/0.99  --qbf_split                             512
% 2.58/0.99  
% 2.58/0.99  ------ BMC1 Options
% 2.58/0.99  
% 2.58/0.99  --bmc1_incremental                      false
% 2.58/0.99  --bmc1_axioms                           reachable_all
% 2.58/0.99  --bmc1_min_bound                        0
% 2.58/0.99  --bmc1_max_bound                        -1
% 2.58/0.99  --bmc1_max_bound_default                -1
% 2.58/0.99  --bmc1_symbol_reachability              true
% 2.58/0.99  --bmc1_property_lemmas                  false
% 2.58/0.99  --bmc1_k_induction                      false
% 2.58/0.99  --bmc1_non_equiv_states                 false
% 2.58/0.99  --bmc1_deadlock                         false
% 2.58/0.99  --bmc1_ucm                              false
% 2.58/0.99  --bmc1_add_unsat_core                   none
% 2.58/0.99  --bmc1_unsat_core_children              false
% 2.58/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.58/0.99  --bmc1_out_stat                         full
% 2.58/0.99  --bmc1_ground_init                      false
% 2.58/0.99  --bmc1_pre_inst_next_state              false
% 2.58/0.99  --bmc1_pre_inst_state                   false
% 2.58/0.99  --bmc1_pre_inst_reach_state             false
% 2.58/0.99  --bmc1_out_unsat_core                   false
% 2.58/0.99  --bmc1_aig_witness_out                  false
% 2.58/0.99  --bmc1_verbose                          false
% 2.58/0.99  --bmc1_dump_clauses_tptp                false
% 2.58/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.58/0.99  --bmc1_dump_file                        -
% 2.58/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.58/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.58/0.99  --bmc1_ucm_extend_mode                  1
% 2.58/0.99  --bmc1_ucm_init_mode                    2
% 2.58/0.99  --bmc1_ucm_cone_mode                    none
% 2.58/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.58/0.99  --bmc1_ucm_relax_model                  4
% 2.58/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.58/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.58/0.99  --bmc1_ucm_layered_model                none
% 2.58/0.99  --bmc1_ucm_max_lemma_size               10
% 2.58/0.99  
% 2.58/0.99  ------ AIG Options
% 2.58/0.99  
% 2.58/0.99  --aig_mode                              false
% 2.58/0.99  
% 2.58/0.99  ------ Instantiation Options
% 2.58/0.99  
% 2.58/0.99  --instantiation_flag                    true
% 2.58/0.99  --inst_sos_flag                         false
% 2.58/0.99  --inst_sos_phase                        true
% 2.58/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.58/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.58/0.99  --inst_lit_sel_side                     num_symb
% 2.58/0.99  --inst_solver_per_active                1400
% 2.58/0.99  --inst_solver_calls_frac                1.
% 2.58/0.99  --inst_passive_queue_type               priority_queues
% 2.58/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.58/0.99  --inst_passive_queues_freq              [25;2]
% 2.58/0.99  --inst_dismatching                      true
% 2.58/0.99  --inst_eager_unprocessed_to_passive     true
% 2.58/0.99  --inst_prop_sim_given                   true
% 2.58/0.99  --inst_prop_sim_new                     false
% 2.58/0.99  --inst_subs_new                         false
% 2.58/0.99  --inst_eq_res_simp                      false
% 2.58/0.99  --inst_subs_given                       false
% 2.58/0.99  --inst_orphan_elimination               true
% 2.58/0.99  --inst_learning_loop_flag               true
% 2.58/0.99  --inst_learning_start                   3000
% 2.58/0.99  --inst_learning_factor                  2
% 2.58/0.99  --inst_start_prop_sim_after_learn       3
% 2.58/0.99  --inst_sel_renew                        solver
% 2.58/0.99  --inst_lit_activity_flag                true
% 2.58/0.99  --inst_restr_to_given                   false
% 2.58/0.99  --inst_activity_threshold               500
% 2.58/0.99  --inst_out_proof                        true
% 2.58/0.99  
% 2.58/0.99  ------ Resolution Options
% 2.58/0.99  
% 2.58/0.99  --resolution_flag                       true
% 2.58/0.99  --res_lit_sel                           adaptive
% 2.58/0.99  --res_lit_sel_side                      none
% 2.58/0.99  --res_ordering                          kbo
% 2.58/0.99  --res_to_prop_solver                    active
% 2.58/0.99  --res_prop_simpl_new                    false
% 2.58/0.99  --res_prop_simpl_given                  true
% 2.58/0.99  --res_passive_queue_type                priority_queues
% 2.58/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.58/0.99  --res_passive_queues_freq               [15;5]
% 2.58/0.99  --res_forward_subs                      full
% 2.58/0.99  --res_backward_subs                     full
% 2.58/0.99  --res_forward_subs_resolution           true
% 2.58/0.99  --res_backward_subs_resolution          true
% 2.58/0.99  --res_orphan_elimination                true
% 2.58/0.99  --res_time_limit                        2.
% 2.58/0.99  --res_out_proof                         true
% 2.58/0.99  
% 2.58/0.99  ------ Superposition Options
% 2.58/0.99  
% 2.58/0.99  --superposition_flag                    true
% 2.58/0.99  --sup_passive_queue_type                priority_queues
% 2.58/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.58/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.58/0.99  --demod_completeness_check              fast
% 2.58/0.99  --demod_use_ground                      true
% 2.58/0.99  --sup_to_prop_solver                    passive
% 2.58/0.99  --sup_prop_simpl_new                    true
% 2.58/0.99  --sup_prop_simpl_given                  true
% 2.58/0.99  --sup_fun_splitting                     false
% 2.58/0.99  --sup_smt_interval                      50000
% 2.58/0.99  
% 2.58/0.99  ------ Superposition Simplification Setup
% 2.58/0.99  
% 2.58/0.99  --sup_indices_passive                   []
% 2.58/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.58/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/0.99  --sup_full_bw                           [BwDemod]
% 2.58/0.99  --sup_immed_triv                        [TrivRules]
% 2.58/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.58/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/0.99  --sup_immed_bw_main                     []
% 2.58/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.58/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/0.99  
% 2.58/0.99  ------ Combination Options
% 2.58/0.99  
% 2.58/0.99  --comb_res_mult                         3
% 2.58/0.99  --comb_sup_mult                         2
% 2.58/0.99  --comb_inst_mult                        10
% 2.58/0.99  
% 2.58/0.99  ------ Debug Options
% 2.58/0.99  
% 2.58/0.99  --dbg_backtrace                         false
% 2.58/0.99  --dbg_dump_prop_clauses                 false
% 2.58/0.99  --dbg_dump_prop_clauses_file            -
% 2.58/0.99  --dbg_out_stat                          false
% 2.58/0.99  ------ Parsing...
% 2.58/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.58/0.99  
% 2.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 2.58/0.99  
% 2.58/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.58/0.99  
% 2.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.58/0.99  ------ Proving...
% 2.58/0.99  ------ Problem Properties 
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  clauses                                 14
% 2.58/0.99  conjectures                             1
% 2.58/0.99  EPR                                     0
% 2.58/0.99  Horn                                    13
% 2.58/0.99  unary                                   6
% 2.58/0.99  binary                                  4
% 2.58/0.99  lits                                    27
% 2.58/0.99  lits eq                                 11
% 2.58/0.99  fd_pure                                 0
% 2.58/0.99  fd_pseudo                               0
% 2.58/0.99  fd_cond                                 0
% 2.58/0.99  fd_pseudo_cond                          0
% 2.58/0.99  AC symbols                              0
% 2.58/0.99  
% 2.58/0.99  ------ Schedule dynamic 5 is on 
% 2.58/0.99  
% 2.58/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  ------ 
% 2.58/0.99  Current options:
% 2.58/0.99  ------ 
% 2.58/0.99  
% 2.58/0.99  ------ Input Options
% 2.58/0.99  
% 2.58/0.99  --out_options                           all
% 2.58/0.99  --tptp_safe_out                         true
% 2.58/0.99  --problem_path                          ""
% 2.58/0.99  --include_path                          ""
% 2.58/0.99  --clausifier                            res/vclausify_rel
% 2.58/0.99  --clausifier_options                    --mode clausify
% 2.58/0.99  --stdin                                 false
% 2.58/0.99  --stats_out                             all
% 2.58/0.99  
% 2.58/0.99  ------ General Options
% 2.58/0.99  
% 2.58/0.99  --fof                                   false
% 2.58/0.99  --time_out_real                         305.
% 2.58/0.99  --time_out_virtual                      -1.
% 2.58/0.99  --symbol_type_check                     false
% 2.58/0.99  --clausify_out                          false
% 2.58/0.99  --sig_cnt_out                           false
% 2.58/0.99  --trig_cnt_out                          false
% 2.58/0.99  --trig_cnt_out_tolerance                1.
% 2.58/0.99  --trig_cnt_out_sk_spl                   false
% 2.58/0.99  --abstr_cl_out                          false
% 2.58/0.99  
% 2.58/0.99  ------ Global Options
% 2.58/0.99  
% 2.58/0.99  --schedule                              default
% 2.58/0.99  --add_important_lit                     false
% 2.58/0.99  --prop_solver_per_cl                    1000
% 2.58/0.99  --min_unsat_core                        false
% 2.58/0.99  --soft_assumptions                      false
% 2.58/0.99  --soft_lemma_size                       3
% 2.58/0.99  --prop_impl_unit_size                   0
% 2.58/0.99  --prop_impl_unit                        []
% 2.58/0.99  --share_sel_clauses                     true
% 2.58/0.99  --reset_solvers                         false
% 2.58/0.99  --bc_imp_inh                            [conj_cone]
% 2.58/0.99  --conj_cone_tolerance                   3.
% 2.58/0.99  --extra_neg_conj                        none
% 2.58/0.99  --large_theory_mode                     true
% 2.58/0.99  --prolific_symb_bound                   200
% 2.58/0.99  --lt_threshold                          2000
% 2.58/0.99  --clause_weak_htbl                      true
% 2.58/0.99  --gc_record_bc_elim                     false
% 2.58/0.99  
% 2.58/0.99  ------ Preprocessing Options
% 2.58/0.99  
% 2.58/0.99  --preprocessing_flag                    true
% 2.58/0.99  --time_out_prep_mult                    0.1
% 2.58/0.99  --splitting_mode                        input
% 2.58/0.99  --splitting_grd                         true
% 2.58/0.99  --splitting_cvd                         false
% 2.58/0.99  --splitting_cvd_svl                     false
% 2.58/0.99  --splitting_nvd                         32
% 2.58/0.99  --sub_typing                            true
% 2.58/0.99  --prep_gs_sim                           true
% 2.58/0.99  --prep_unflatten                        true
% 2.58/0.99  --prep_res_sim                          true
% 2.58/0.99  --prep_upred                            true
% 2.58/0.99  --prep_sem_filter                       exhaustive
% 2.58/0.99  --prep_sem_filter_out                   false
% 2.58/0.99  --pred_elim                             true
% 2.58/0.99  --res_sim_input                         true
% 2.58/0.99  --eq_ax_congr_red                       true
% 2.58/0.99  --pure_diseq_elim                       true
% 2.58/0.99  --brand_transform                       false
% 2.58/0.99  --non_eq_to_eq                          false
% 2.58/0.99  --prep_def_merge                        true
% 2.58/0.99  --prep_def_merge_prop_impl              false
% 2.58/0.99  --prep_def_merge_mbd                    true
% 2.58/0.99  --prep_def_merge_tr_red                 false
% 2.58/0.99  --prep_def_merge_tr_cl                  false
% 2.58/0.99  --smt_preprocessing                     true
% 2.58/0.99  --smt_ac_axioms                         fast
% 2.58/0.99  --preprocessed_out                      false
% 2.58/0.99  --preprocessed_stats                    false
% 2.58/0.99  
% 2.58/0.99  ------ Abstraction refinement Options
% 2.58/0.99  
% 2.58/0.99  --abstr_ref                             []
% 2.58/0.99  --abstr_ref_prep                        false
% 2.58/0.99  --abstr_ref_until_sat                   false
% 2.58/0.99  --abstr_ref_sig_restrict                funpre
% 2.58/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.58/0.99  --abstr_ref_under                       []
% 2.58/0.99  
% 2.58/0.99  ------ SAT Options
% 2.58/0.99  
% 2.58/0.99  --sat_mode                              false
% 2.58/0.99  --sat_fm_restart_options                ""
% 2.58/0.99  --sat_gr_def                            false
% 2.58/0.99  --sat_epr_types                         true
% 2.58/0.99  --sat_non_cyclic_types                  false
% 2.58/0.99  --sat_finite_models                     false
% 2.58/0.99  --sat_fm_lemmas                         false
% 2.58/0.99  --sat_fm_prep                           false
% 2.58/0.99  --sat_fm_uc_incr                        true
% 2.58/0.99  --sat_out_model                         small
% 2.58/0.99  --sat_out_clauses                       false
% 2.58/0.99  
% 2.58/0.99  ------ QBF Options
% 2.58/0.99  
% 2.58/0.99  --qbf_mode                              false
% 2.58/0.99  --qbf_elim_univ                         false
% 2.58/0.99  --qbf_dom_inst                          none
% 2.58/0.99  --qbf_dom_pre_inst                      false
% 2.58/0.99  --qbf_sk_in                             false
% 2.58/0.99  --qbf_pred_elim                         true
% 2.58/0.99  --qbf_split                             512
% 2.58/0.99  
% 2.58/0.99  ------ BMC1 Options
% 2.58/0.99  
% 2.58/0.99  --bmc1_incremental                      false
% 2.58/0.99  --bmc1_axioms                           reachable_all
% 2.58/0.99  --bmc1_min_bound                        0
% 2.58/0.99  --bmc1_max_bound                        -1
% 2.58/0.99  --bmc1_max_bound_default                -1
% 2.58/0.99  --bmc1_symbol_reachability              true
% 2.58/0.99  --bmc1_property_lemmas                  false
% 2.58/0.99  --bmc1_k_induction                      false
% 2.58/0.99  --bmc1_non_equiv_states                 false
% 2.58/0.99  --bmc1_deadlock                         false
% 2.58/0.99  --bmc1_ucm                              false
% 2.58/0.99  --bmc1_add_unsat_core                   none
% 2.58/0.99  --bmc1_unsat_core_children              false
% 2.58/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.58/0.99  --bmc1_out_stat                         full
% 2.58/0.99  --bmc1_ground_init                      false
% 2.58/0.99  --bmc1_pre_inst_next_state              false
% 2.58/0.99  --bmc1_pre_inst_state                   false
% 2.58/0.99  --bmc1_pre_inst_reach_state             false
% 2.58/0.99  --bmc1_out_unsat_core                   false
% 2.58/0.99  --bmc1_aig_witness_out                  false
% 2.58/0.99  --bmc1_verbose                          false
% 2.58/0.99  --bmc1_dump_clauses_tptp                false
% 2.58/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.58/0.99  --bmc1_dump_file                        -
% 2.58/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.58/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.58/0.99  --bmc1_ucm_extend_mode                  1
% 2.58/0.99  --bmc1_ucm_init_mode                    2
% 2.58/0.99  --bmc1_ucm_cone_mode                    none
% 2.58/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.58/0.99  --bmc1_ucm_relax_model                  4
% 2.58/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.58/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.58/0.99  --bmc1_ucm_layered_model                none
% 2.58/0.99  --bmc1_ucm_max_lemma_size               10
% 2.58/0.99  
% 2.58/0.99  ------ AIG Options
% 2.58/0.99  
% 2.58/0.99  --aig_mode                              false
% 2.58/0.99  
% 2.58/0.99  ------ Instantiation Options
% 2.58/0.99  
% 2.58/0.99  --instantiation_flag                    true
% 2.58/0.99  --inst_sos_flag                         false
% 2.58/0.99  --inst_sos_phase                        true
% 2.58/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.58/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.58/0.99  --inst_lit_sel_side                     none
% 2.58/0.99  --inst_solver_per_active                1400
% 2.58/0.99  --inst_solver_calls_frac                1.
% 2.58/0.99  --inst_passive_queue_type               priority_queues
% 2.58/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.58/0.99  --inst_passive_queues_freq              [25;2]
% 2.58/0.99  --inst_dismatching                      true
% 2.58/0.99  --inst_eager_unprocessed_to_passive     true
% 2.58/0.99  --inst_prop_sim_given                   true
% 2.58/0.99  --inst_prop_sim_new                     false
% 2.58/0.99  --inst_subs_new                         false
% 2.58/0.99  --inst_eq_res_simp                      false
% 2.58/0.99  --inst_subs_given                       false
% 2.58/0.99  --inst_orphan_elimination               true
% 2.58/0.99  --inst_learning_loop_flag               true
% 2.58/0.99  --inst_learning_start                   3000
% 2.58/0.99  --inst_learning_factor                  2
% 2.58/0.99  --inst_start_prop_sim_after_learn       3
% 2.58/0.99  --inst_sel_renew                        solver
% 2.58/0.99  --inst_lit_activity_flag                true
% 2.58/0.99  --inst_restr_to_given                   false
% 2.58/0.99  --inst_activity_threshold               500
% 2.58/0.99  --inst_out_proof                        true
% 2.58/0.99  
% 2.58/0.99  ------ Resolution Options
% 2.58/0.99  
% 2.58/0.99  --resolution_flag                       false
% 2.58/0.99  --res_lit_sel                           adaptive
% 2.58/0.99  --res_lit_sel_side                      none
% 2.58/0.99  --res_ordering                          kbo
% 2.58/0.99  --res_to_prop_solver                    active
% 2.58/0.99  --res_prop_simpl_new                    false
% 2.58/0.99  --res_prop_simpl_given                  true
% 2.58/0.99  --res_passive_queue_type                priority_queues
% 2.58/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.58/0.99  --res_passive_queues_freq               [15;5]
% 2.58/0.99  --res_forward_subs                      full
% 2.58/0.99  --res_backward_subs                     full
% 2.58/0.99  --res_forward_subs_resolution           true
% 2.58/0.99  --res_backward_subs_resolution          true
% 2.58/0.99  --res_orphan_elimination                true
% 2.58/0.99  --res_time_limit                        2.
% 2.58/0.99  --res_out_proof                         true
% 2.58/0.99  
% 2.58/0.99  ------ Superposition Options
% 2.58/0.99  
% 2.58/0.99  --superposition_flag                    true
% 2.58/0.99  --sup_passive_queue_type                priority_queues
% 2.58/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.58/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.58/0.99  --demod_completeness_check              fast
% 2.58/0.99  --demod_use_ground                      true
% 2.58/0.99  --sup_to_prop_solver                    passive
% 2.58/0.99  --sup_prop_simpl_new                    true
% 2.58/0.99  --sup_prop_simpl_given                  true
% 2.58/0.99  --sup_fun_splitting                     false
% 2.58/0.99  --sup_smt_interval                      50000
% 2.58/0.99  
% 2.58/0.99  ------ Superposition Simplification Setup
% 2.58/0.99  
% 2.58/0.99  --sup_indices_passive                   []
% 2.58/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.58/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/0.99  --sup_full_bw                           [BwDemod]
% 2.58/0.99  --sup_immed_triv                        [TrivRules]
% 2.58/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.58/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/0.99  --sup_immed_bw_main                     []
% 2.58/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.58/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/0.99  
% 2.58/0.99  ------ Combination Options
% 2.58/0.99  
% 2.58/0.99  --comb_res_mult                         3
% 2.58/0.99  --comb_sup_mult                         2
% 2.58/0.99  --comb_inst_mult                        10
% 2.58/0.99  
% 2.58/0.99  ------ Debug Options
% 2.58/0.99  
% 2.58/0.99  --dbg_backtrace                         false
% 2.58/0.99  --dbg_dump_prop_clauses                 false
% 2.58/0.99  --dbg_dump_prop_clauses_file            -
% 2.58/0.99  --dbg_out_stat                          false
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  ------ Proving...
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  % SZS status Theorem for theBenchmark.p
% 2.58/0.99  
% 2.58/0.99   Resolution empty clause
% 2.58/0.99  
% 2.58/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.58/0.99  
% 2.58/0.99  fof(f17,conjecture,(
% 2.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f18,negated_conjecture,(
% 2.58/0.99    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 2.58/0.99    inference(negated_conjecture,[],[f17])).
% 2.58/0.99  
% 2.58/0.99  fof(f34,plain,(
% 2.58/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.58/0.99    inference(ennf_transformation,[],[f18])).
% 2.58/0.99  
% 2.58/0.99  fof(f35,plain,(
% 2.58/0.99    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.58/0.99    inference(flattening,[],[f34])).
% 2.58/0.99  
% 2.58/0.99  fof(f43,plain,(
% 2.58/0.99    ( ! [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_subset_1(sK2,u1_struct_0(X0)) & v3_tex_2(sK2,X0) & (v4_pre_topc(sK2,X0) | v3_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.58/0.99    introduced(choice_axiom,[])).
% 2.58/0.99  
% 2.58/0.99  fof(f42,plain,(
% 2.58/0.99    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v1_subset_1(X1,u1_struct_0(sK1)) & v3_tex_2(X1,sK1) & (v4_pre_topc(X1,sK1) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.58/0.99    introduced(choice_axiom,[])).
% 2.58/0.99  
% 2.58/0.99  fof(f44,plain,(
% 2.58/0.99    (v1_subset_1(sK2,u1_struct_0(sK1)) & v3_tex_2(sK2,sK1) & (v4_pre_topc(sK2,sK1) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f35,f43,f42])).
% 2.58/0.99  
% 2.58/0.99  fof(f71,plain,(
% 2.58/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.58/0.99    inference(cnf_transformation,[],[f44])).
% 2.58/0.99  
% 2.58/0.99  fof(f11,axiom,(
% 2.58/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f24,plain,(
% 2.58/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.58/0.99    inference(ennf_transformation,[],[f11])).
% 2.58/0.99  
% 2.58/0.99  fof(f25,plain,(
% 2.58/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.58/0.99    inference(flattening,[],[f24])).
% 2.58/0.99  
% 2.58/0.99  fof(f55,plain,(
% 2.58/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f25])).
% 2.58/0.99  
% 2.58/0.99  fof(f70,plain,(
% 2.58/0.99    l1_pre_topc(sK1)),
% 2.58/0.99    inference(cnf_transformation,[],[f44])).
% 2.58/0.99  
% 2.58/0.99  fof(f13,axiom,(
% 2.58/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f27,plain,(
% 2.58/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.58/0.99    inference(ennf_transformation,[],[f13])).
% 2.58/0.99  
% 2.58/0.99  fof(f37,plain,(
% 2.58/0.99    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.58/0.99    inference(nnf_transformation,[],[f27])).
% 2.58/0.99  
% 2.58/0.99  fof(f59,plain,(
% 2.58/0.99    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f37])).
% 2.58/0.99  
% 2.58/0.99  fof(f16,axiom,(
% 2.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f32,plain,(
% 2.58/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.58/0.99    inference(ennf_transformation,[],[f16])).
% 2.58/0.99  
% 2.58/0.99  fof(f33,plain,(
% 2.58/0.99    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.58/0.99    inference(flattening,[],[f32])).
% 2.58/0.99  
% 2.58/0.99  fof(f66,plain,(
% 2.58/0.99    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f33])).
% 2.58/0.99  
% 2.58/0.99  fof(f73,plain,(
% 2.58/0.99    v3_tex_2(sK2,sK1)),
% 2.58/0.99    inference(cnf_transformation,[],[f44])).
% 2.58/0.99  
% 2.58/0.99  fof(f67,plain,(
% 2.58/0.99    ~v2_struct_0(sK1)),
% 2.58/0.99    inference(cnf_transformation,[],[f44])).
% 2.58/0.99  
% 2.58/0.99  fof(f68,plain,(
% 2.58/0.99    v2_pre_topc(sK1)),
% 2.58/0.99    inference(cnf_transformation,[],[f44])).
% 2.58/0.99  
% 2.58/0.99  fof(f15,axiom,(
% 2.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f30,plain,(
% 2.58/0.99    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.58/0.99    inference(ennf_transformation,[],[f15])).
% 2.58/0.99  
% 2.58/0.99  fof(f31,plain,(
% 2.58/0.99    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.58/0.99    inference(flattening,[],[f30])).
% 2.58/0.99  
% 2.58/0.99  fof(f38,plain,(
% 2.58/0.99    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.58/0.99    inference(nnf_transformation,[],[f31])).
% 2.58/0.99  
% 2.58/0.99  fof(f39,plain,(
% 2.58/0.99    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.58/0.99    inference(rectify,[],[f38])).
% 2.58/0.99  
% 2.58/0.99  fof(f40,plain,(
% 2.58/0.99    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK0(X0),X0) & v4_pre_topc(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.58/0.99    introduced(choice_axiom,[])).
% 2.58/0.99  
% 2.58/0.99  fof(f41,plain,(
% 2.58/0.99    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK0(X0),X0) & v4_pre_topc(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 2.58/0.99  
% 2.58/0.99  fof(f62,plain,(
% 2.58/0.99    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f41])).
% 2.58/0.99  
% 2.58/0.99  fof(f69,plain,(
% 2.58/0.99    v3_tdlat_3(sK1)),
% 2.58/0.99    inference(cnf_transformation,[],[f44])).
% 2.58/0.99  
% 2.58/0.99  fof(f72,plain,(
% 2.58/0.99    v4_pre_topc(sK2,sK1) | v3_pre_topc(sK2,sK1)),
% 2.58/0.99    inference(cnf_transformation,[],[f44])).
% 2.58/0.99  
% 2.58/0.99  fof(f12,axiom,(
% 2.58/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f26,plain,(
% 2.58/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.58/0.99    inference(ennf_transformation,[],[f12])).
% 2.58/0.99  
% 2.58/0.99  fof(f36,plain,(
% 2.58/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.58/0.99    inference(nnf_transformation,[],[f26])).
% 2.58/0.99  
% 2.58/0.99  fof(f58,plain,(
% 2.58/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f36])).
% 2.58/0.99  
% 2.58/0.99  fof(f8,axiom,(
% 2.58/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f21,plain,(
% 2.58/0.99    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.58/0.99    inference(ennf_transformation,[],[f8])).
% 2.58/0.99  
% 2.58/0.99  fof(f52,plain,(
% 2.58/0.99    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.58/0.99    inference(cnf_transformation,[],[f21])).
% 2.58/0.99  
% 2.58/0.99  fof(f9,axiom,(
% 2.58/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f22,plain,(
% 2.58/0.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.58/0.99    inference(ennf_transformation,[],[f9])).
% 2.58/0.99  
% 2.58/0.99  fof(f53,plain,(
% 2.58/0.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.58/0.99    inference(cnf_transformation,[],[f22])).
% 2.58/0.99  
% 2.58/0.99  fof(f7,axiom,(
% 2.58/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f20,plain,(
% 2.58/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.58/0.99    inference(ennf_transformation,[],[f7])).
% 2.58/0.99  
% 2.58/0.99  fof(f51,plain,(
% 2.58/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.58/0.99    inference(cnf_transformation,[],[f20])).
% 2.58/0.99  
% 2.58/0.99  fof(f3,axiom,(
% 2.58/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f47,plain,(
% 2.58/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f3])).
% 2.58/0.99  
% 2.58/0.99  fof(f6,axiom,(
% 2.58/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f50,plain,(
% 2.58/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.58/0.99    inference(cnf_transformation,[],[f6])).
% 2.58/0.99  
% 2.58/0.99  fof(f76,plain,(
% 2.58/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 2.58/0.99    inference(definition_unfolding,[],[f47,f50])).
% 2.58/0.99  
% 2.58/0.99  fof(f5,axiom,(
% 2.58/0.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f19,plain,(
% 2.58/0.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.58/0.99    inference(ennf_transformation,[],[f5])).
% 2.58/0.99  
% 2.58/0.99  fof(f49,plain,(
% 2.58/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f19])).
% 2.58/0.99  
% 2.58/0.99  fof(f4,axiom,(
% 2.58/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f48,plain,(
% 2.58/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.58/0.99    inference(cnf_transformation,[],[f4])).
% 2.58/0.99  
% 2.58/0.99  fof(f1,axiom,(
% 2.58/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f45,plain,(
% 2.58/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f1])).
% 2.58/0.99  
% 2.58/0.99  fof(f75,plain,(
% 2.58/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.58/0.99    inference(definition_unfolding,[],[f45,f50,f50])).
% 2.58/0.99  
% 2.58/0.99  fof(f2,axiom,(
% 2.58/0.99    v1_xboole_0(k1_xboole_0)),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f46,plain,(
% 2.58/0.99    v1_xboole_0(k1_xboole_0)),
% 2.58/0.99    inference(cnf_transformation,[],[f2])).
% 2.58/0.99  
% 2.58/0.99  fof(f14,axiom,(
% 2.58/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & v1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k3_subset_1(X0,X1)))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f28,plain,(
% 2.58/0.99    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.58/0.99    inference(ennf_transformation,[],[f14])).
% 2.58/0.99  
% 2.58/0.99  fof(f29,plain,(
% 2.58/0.99    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.58/0.99    inference(flattening,[],[f28])).
% 2.58/0.99  
% 2.58/0.99  fof(f61,plain,(
% 2.58/0.99    ( ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f29])).
% 2.58/0.99  
% 2.58/0.99  fof(f10,axiom,(
% 2.58/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f23,plain,(
% 2.58/0.99    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.58/0.99    inference(ennf_transformation,[],[f10])).
% 2.58/0.99  
% 2.58/0.99  fof(f54,plain,(
% 2.58/0.99    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f23])).
% 2.58/0.99  
% 2.58/0.99  fof(f74,plain,(
% 2.58/0.99    v1_subset_1(sK2,u1_struct_0(sK1))),
% 2.58/0.99    inference(cnf_transformation,[],[f44])).
% 2.58/0.99  
% 2.58/0.99  cnf(c_24,negated_conjecture,
% 2.58/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.58/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_841,plain,
% 2.58/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_10,plain,
% 2.58/0.99      ( ~ v4_pre_topc(X0,X1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.58/0.99      | ~ l1_pre_topc(X1)
% 2.58/0.99      | k2_pre_topc(X1,X0) = X0 ),
% 2.58/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_25,negated_conjecture,
% 2.58/0.99      ( l1_pre_topc(sK1) ),
% 2.58/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_489,plain,
% 2.58/0.99      ( ~ v4_pre_topc(X0,X1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.58/0.99      | k2_pre_topc(X1,X0) = X0
% 2.58/0.99      | sK1 != X1 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_490,plain,
% 2.58/0.99      ( ~ v4_pre_topc(X0,sK1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.58/0.99      | k2_pre_topc(sK1,X0) = X0 ),
% 2.58/0.99      inference(unflattening,[status(thm)],[c_489]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_838,plain,
% 2.58/0.99      ( k2_pre_topc(sK1,X0) = X0
% 2.58/0.99      | v4_pre_topc(X0,sK1) != iProver_top
% 2.58/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_490]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1003,plain,
% 2.58/0.99      ( k2_pre_topc(sK1,sK2) = sK2 | v4_pre_topc(sK2,sK1) != iProver_top ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_841,c_838]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_14,plain,
% 2.58/0.99      ( ~ v1_tops_1(X0,X1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.58/0.99      | ~ l1_pre_topc(X1)
% 2.58/0.99      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 2.58/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_20,plain,
% 2.58/0.99      ( ~ v3_tex_2(X0,X1)
% 2.58/0.99      | v1_tops_1(X0,X1)
% 2.58/0.99      | ~ v3_pre_topc(X0,X1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.58/0.99      | v2_struct_0(X1)
% 2.58/0.99      | ~ l1_pre_topc(X1)
% 2.58/0.99      | ~ v2_pre_topc(X1) ),
% 2.58/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_22,negated_conjecture,
% 2.58/0.99      ( v3_tex_2(sK2,sK1) ),
% 2.58/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_368,plain,
% 2.58/0.99      ( v1_tops_1(X0,X1)
% 2.58/0.99      | ~ v3_pre_topc(X0,X1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.58/0.99      | v2_struct_0(X1)
% 2.58/0.99      | ~ l1_pre_topc(X1)
% 2.58/0.99      | ~ v2_pre_topc(X1)
% 2.58/0.99      | sK1 != X1
% 2.58/0.99      | sK2 != X0 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_22]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_369,plain,
% 2.58/0.99      ( v1_tops_1(sK2,sK1)
% 2.58/0.99      | ~ v3_pre_topc(sK2,sK1)
% 2.58/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.58/0.99      | v2_struct_0(sK1)
% 2.58/0.99      | ~ l1_pre_topc(sK1)
% 2.58/0.99      | ~ v2_pre_topc(sK1) ),
% 2.58/0.99      inference(unflattening,[status(thm)],[c_368]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_28,negated_conjecture,
% 2.58/0.99      ( ~ v2_struct_0(sK1) ),
% 2.58/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_27,negated_conjecture,
% 2.58/0.99      ( v2_pre_topc(sK1) ),
% 2.58/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_371,plain,
% 2.58/0.99      ( v1_tops_1(sK2,sK1) | ~ v3_pre_topc(sK2,sK1) ),
% 2.58/0.99      inference(global_propositional_subsumption,
% 2.58/0.99                [status(thm)],
% 2.58/0.99                [c_369,c_28,c_27,c_25,c_24]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_386,plain,
% 2.58/0.99      ( ~ v3_pre_topc(sK2,sK1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.58/0.99      | ~ l1_pre_topc(X1)
% 2.58/0.99      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 2.58/0.99      | sK1 != X1
% 2.58/0.99      | sK2 != X0 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_371]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_387,plain,
% 2.58/0.99      ( ~ v3_pre_topc(sK2,sK1)
% 2.58/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.58/0.99      | ~ l1_pre_topc(sK1)
% 2.58/0.99      | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 2.58/0.99      inference(unflattening,[status(thm)],[c_386]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_389,plain,
% 2.58/0.99      ( ~ v3_pre_topc(sK2,sK1) | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 2.58/0.99      inference(global_propositional_subsumption,
% 2.58/0.99                [status(thm)],
% 2.58/0.99                [c_387,c_25,c_24]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_19,plain,
% 2.58/0.99      ( v3_pre_topc(X0,X1)
% 2.58/0.99      | ~ v4_pre_topc(X0,X1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.58/0.99      | ~ v3_tdlat_3(X1)
% 2.58/0.99      | ~ l1_pre_topc(X1)
% 2.58/0.99      | ~ v2_pre_topc(X1) ),
% 2.58/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_409,plain,
% 2.58/0.99      ( v3_pre_topc(X0,X1)
% 2.58/0.99      | ~ v4_pre_topc(X0,X1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.58/0.99      | ~ v3_tdlat_3(X1)
% 2.58/0.99      | ~ l1_pre_topc(X1)
% 2.58/0.99      | sK1 != X1 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_410,plain,
% 2.58/0.99      ( v3_pre_topc(X0,sK1)
% 2.58/0.99      | ~ v4_pre_topc(X0,sK1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.58/0.99      | ~ v3_tdlat_3(sK1)
% 2.58/0.99      | ~ l1_pre_topc(sK1) ),
% 2.58/0.99      inference(unflattening,[status(thm)],[c_409]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_26,negated_conjecture,
% 2.58/0.99      ( v3_tdlat_3(sK1) ),
% 2.58/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_414,plain,
% 2.58/0.99      ( v3_pre_topc(X0,sK1)
% 2.58/0.99      | ~ v4_pre_topc(X0,sK1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.58/0.99      inference(global_propositional_subsumption,
% 2.58/0.99                [status(thm)],
% 2.58/0.99                [c_410,c_26,c_25]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_526,plain,
% 2.58/0.99      ( ~ v4_pre_topc(X0,sK1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.58/0.99      | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
% 2.58/0.99      | sK1 != sK1
% 2.58/0.99      | sK2 != X0 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_389,c_414]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_527,plain,
% 2.58/0.99      ( ~ v4_pre_topc(sK2,sK1)
% 2.58/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.58/0.99      | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 2.58/0.99      inference(unflattening,[status(thm)],[c_526]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_23,negated_conjecture,
% 2.58/0.99      ( v3_pre_topc(sK2,sK1) | v4_pre_topc(sK2,sK1) ),
% 2.58/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_516,plain,
% 2.58/0.99      ( v4_pre_topc(sK2,sK1) | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 2.58/0.99      inference(resolution,[status(thm)],[c_23,c_389]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_529,plain,
% 2.58/0.99      ( k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 2.58/0.99      inference(global_propositional_subsumption,
% 2.58/0.99                [status(thm)],
% 2.58/0.99                [c_527,c_24,c_516]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1004,plain,
% 2.58/0.99      ( u1_struct_0(sK1) = sK2 | v4_pre_topc(sK2,sK1) != iProver_top ),
% 2.58/0.99      inference(demodulation,[status(thm)],[c_1003,c_529]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_33,plain,
% 2.58/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_11,plain,
% 2.58/0.99      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 2.58/0.99      | v4_pre_topc(X1,X0)
% 2.58/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.58/0.99      | ~ l1_pre_topc(X0) ),
% 2.58/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_474,plain,
% 2.58/0.99      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 2.58/0.99      | v4_pre_topc(X1,X0)
% 2.58/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.58/0.99      | sK1 != X0 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_475,plain,
% 2.58/0.99      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
% 2.58/0.99      | v4_pre_topc(X0,sK1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.58/0.99      inference(unflattening,[status(thm)],[c_474]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_555,plain,
% 2.58/0.99      ( ~ v4_pre_topc(X0,sK1)
% 2.58/0.99      | v4_pre_topc(X1,sK1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.58/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.58/0.99      | k3_subset_1(u1_struct_0(sK1),X1) != X0
% 2.58/0.99      | sK1 != sK1 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_414,c_475]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_556,plain,
% 2.58/0.99      ( v4_pre_topc(X0,sK1)
% 2.58/0.99      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.58/0.99      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.58/0.99      inference(unflattening,[status(thm)],[c_555]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_6,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.58/0.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.58/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_568,plain,
% 2.58/0.99      ( v4_pre_topc(X0,sK1)
% 2.58/0.99      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.58/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_556,c_6]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_925,plain,
% 2.58/0.99      ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 2.58/0.99      | v4_pre_topc(sK2,sK1)
% 2.58/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_568]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_926,plain,
% 2.58/0.99      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) != iProver_top
% 2.58/0.99      | v4_pre_topc(sK2,sK1) = iProver_top
% 2.58/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_925]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_931,plain,
% 2.58/0.99      ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.58/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_932,plain,
% 2.58/0.99      ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.58/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_931]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_7,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.58/0.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 2.58/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_937,plain,
% 2.58/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.58/0.99      | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) = sK2 ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_534,plain,
% 2.58/0.99      ( v4_pre_topc(X0,sK1)
% 2.58/0.99      | v4_pre_topc(sK2,sK1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.58/0.99      | k3_subset_1(u1_struct_0(sK1),X0) != sK2
% 2.58/0.99      | sK1 != sK1 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_475]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_596,plain,
% 2.58/0.99      ( v4_pre_topc(X0,sK1)
% 2.58/0.99      | v4_pre_topc(sK2,sK1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.58/0.99      | k3_subset_1(u1_struct_0(sK1),X0) != sK2 ),
% 2.58/0.99      inference(equality_resolution_simp,[status(thm)],[c_534]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1020,plain,
% 2.58/0.99      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 2.58/0.99      | v4_pre_topc(sK2,sK1)
% 2.58/0.99      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.58/0.99      | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) != sK2 ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_596]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1021,plain,
% 2.58/0.99      ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) != sK2
% 2.58/0.99      | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
% 2.58/0.99      | v4_pre_topc(sK2,sK1) = iProver_top
% 2.58/0.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_1020]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1044,plain,
% 2.58/0.99      ( u1_struct_0(sK1) = sK2 ),
% 2.58/0.99      inference(global_propositional_subsumption,
% 2.58/0.99                [status(thm)],
% 2.58/0.99                [c_1004,c_24,c_33,c_926,c_932,c_937,c_1021]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1051,plain,
% 2.58/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK2)) = iProver_top ),
% 2.58/0.99      inference(demodulation,[status(thm)],[c_1044,c_841]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_5,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.58/0.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 2.58/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_844,plain,
% 2.58/0.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 2.58/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1751,plain,
% 2.58/0.99      ( k3_subset_1(sK2,sK2) = k4_xboole_0(sK2,sK2) ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_1051,c_844]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2,plain,
% 2.58/0.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 2.58/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_4,plain,
% 2.58/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.58/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_306,plain,
% 2.58/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2
% 2.58/0.99      | k1_xboole_0 != X0
% 2.58/0.99      | k1_xboole_0 = X2 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_4]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_307,plain,
% 2.58/0.99      ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 2.58/0.99      inference(unflattening,[status(thm)],[c_306]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_3,plain,
% 2.58/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.58/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_0,plain,
% 2.58/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 2.58/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1231,plain,
% 2.58/0.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1820,plain,
% 2.58/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.58/0.99      inference(demodulation,[status(thm)],[c_307,c_1231]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1942,plain,
% 2.58/0.99      ( k3_subset_1(sK2,sK2) = k1_xboole_0 ),
% 2.58/0.99      inference(demodulation,[status(thm)],[c_1751,c_1820]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1,plain,
% 2.58/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.58/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_15,plain,
% 2.58/0.99      ( ~ v1_subset_1(X0,X1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.58/0.99      | v1_xboole_0(X1)
% 2.58/0.99      | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
% 2.58/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_8,plain,
% 2.58/0.99      ( ~ v1_subset_1(X0,X1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.58/0.99      | ~ v1_xboole_0(X1) ),
% 2.58/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_156,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.58/0.99      | ~ v1_subset_1(X0,X1)
% 2.58/0.99      | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
% 2.58/0.99      inference(global_propositional_subsumption,[status(thm)],[c_15,c_8]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_157,plain,
% 2.58/0.99      ( ~ v1_subset_1(X0,X1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.58/0.99      | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
% 2.58/0.99      inference(renaming,[status(thm)],[c_156]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_325,plain,
% 2.58/0.99      ( ~ v1_subset_1(X0,X1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.58/0.99      | k3_subset_1(X1,X0) != k1_xboole_0 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_157]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_21,negated_conjecture,
% 2.58/0.99      ( v1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.58/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_346,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.58/0.99      | k3_subset_1(X1,X0) != k1_xboole_0
% 2.58/0.99      | u1_struct_0(sK1) != X1
% 2.58/0.99      | sK2 != X0 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_325,c_21]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_347,plain,
% 2.58/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.58/0.99      | k3_subset_1(u1_struct_0(sK1),sK2) != k1_xboole_0 ),
% 2.58/0.99      inference(unflattening,[status(thm)],[c_346]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_349,plain,
% 2.58/0.99      ( k3_subset_1(u1_struct_0(sK1),sK2) != k1_xboole_0 ),
% 2.58/0.99      inference(global_propositional_subsumption,[status(thm)],[c_347,c_24]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1052,plain,
% 2.58/0.99      ( k3_subset_1(sK2,sK2) != k1_xboole_0 ),
% 2.58/0.99      inference(demodulation,[status(thm)],[c_1044,c_349]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1944,plain,
% 2.58/0.99      ( $false ),
% 2.58/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_1942,c_1052]) ).
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.58/0.99  
% 2.58/0.99  ------                               Statistics
% 2.58/0.99  
% 2.58/0.99  ------ General
% 2.58/0.99  
% 2.58/0.99  abstr_ref_over_cycles:                  0
% 2.58/0.99  abstr_ref_under_cycles:                 0
% 2.58/0.99  gc_basic_clause_elim:                   0
% 2.58/0.99  forced_gc_time:                         0
% 2.58/0.99  parsing_time:                           0.008
% 2.58/0.99  unif_index_cands_time:                  0.
% 2.58/0.99  unif_index_add_time:                    0.
% 2.58/0.99  orderings_time:                         0.
% 2.58/0.99  out_proof_time:                         0.011
% 2.58/0.99  total_time:                             0.108
% 2.58/0.99  num_of_symbols:                         52
% 2.58/0.99  num_of_terms:                           1508
% 2.58/0.99  
% 2.58/0.99  ------ Preprocessing
% 2.58/0.99  
% 2.58/0.99  num_of_splits:                          0
% 2.58/0.99  num_of_split_atoms:                     0
% 2.58/0.99  num_of_reused_defs:                     0
% 2.58/0.99  num_eq_ax_congr_red:                    6
% 2.58/0.99  num_of_sem_filtered_clauses:            1
% 2.58/0.99  num_of_subtypes:                        0
% 2.58/0.99  monotx_restored_types:                  0
% 2.58/0.99  sat_num_of_epr_types:                   0
% 2.58/0.99  sat_num_of_non_cyclic_types:            0
% 2.58/0.99  sat_guarded_non_collapsed_types:        0
% 2.58/0.99  num_pure_diseq_elim:                    0
% 2.58/0.99  simp_replaced_by:                       0
% 2.58/0.99  res_preprocessed:                       90
% 2.58/0.99  prep_upred:                             0
% 2.58/0.99  prep_unflattend:                        20
% 2.58/0.99  smt_new_axioms:                         0
% 2.58/0.99  pred_elim_cands:                        2
% 2.58/0.99  pred_elim:                              10
% 2.58/0.99  pred_elim_cl:                           15
% 2.58/0.99  pred_elim_cycles:                       12
% 2.58/0.99  merged_defs:                            0
% 2.58/0.99  merged_defs_ncl:                        0
% 2.58/0.99  bin_hyper_res:                          0
% 2.58/0.99  prep_cycles:                            4
% 2.58/0.99  pred_elim_time:                         0.006
% 2.58/0.99  splitting_time:                         0.
% 2.58/0.99  sem_filter_time:                        0.
% 2.58/0.99  monotx_time:                            0.001
% 2.58/0.99  subtype_inf_time:                       0.
% 2.58/0.99  
% 2.58/0.99  ------ Problem properties
% 2.58/0.99  
% 2.58/0.99  clauses:                                14
% 2.58/0.99  conjectures:                            1
% 2.58/0.99  epr:                                    0
% 2.58/0.99  horn:                                   13
% 2.58/0.99  ground:                                 4
% 2.58/0.99  unary:                                  6
% 2.58/0.99  binary:                                 4
% 2.58/0.99  lits:                                   27
% 2.58/0.99  lits_eq:                                11
% 2.58/0.99  fd_pure:                                0
% 2.58/0.99  fd_pseudo:                              0
% 2.58/0.99  fd_cond:                                0
% 2.58/0.99  fd_pseudo_cond:                         0
% 2.58/0.99  ac_symbols:                             0
% 2.58/0.99  
% 2.58/0.99  ------ Propositional Solver
% 2.58/0.99  
% 2.58/0.99  prop_solver_calls:                      28
% 2.58/0.99  prop_fast_solver_calls:                 540
% 2.58/0.99  smt_solver_calls:                       0
% 2.58/0.99  smt_fast_solver_calls:                  0
% 2.58/0.99  prop_num_of_clauses:                    716
% 2.58/0.99  prop_preprocess_simplified:             2812
% 2.58/0.99  prop_fo_subsumed:                       19
% 2.58/0.99  prop_solver_time:                       0.
% 2.58/0.99  smt_solver_time:                        0.
% 2.58/0.99  smt_fast_solver_time:                   0.
% 2.58/0.99  prop_fast_solver_time:                  0.
% 2.58/0.99  prop_unsat_core_time:                   0.
% 2.58/0.99  
% 2.58/0.99  ------ QBF
% 2.58/0.99  
% 2.58/0.99  qbf_q_res:                              0
% 2.58/0.99  qbf_num_tautologies:                    0
% 2.58/0.99  qbf_prep_cycles:                        0
% 2.58/0.99  
% 2.58/0.99  ------ BMC1
% 2.58/0.99  
% 2.58/0.99  bmc1_current_bound:                     -1
% 2.58/0.99  bmc1_last_solved_bound:                 -1
% 2.58/0.99  bmc1_unsat_core_size:                   -1
% 2.58/0.99  bmc1_unsat_core_parents_size:           -1
% 2.58/0.99  bmc1_merge_next_fun:                    0
% 2.58/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.58/0.99  
% 2.58/0.99  ------ Instantiation
% 2.58/0.99  
% 2.58/0.99  inst_num_of_clauses:                    230
% 2.58/0.99  inst_num_in_passive:                    87
% 2.58/0.99  inst_num_in_active:                     118
% 2.58/0.99  inst_num_in_unprocessed:                25
% 2.58/0.99  inst_num_of_loops:                      130
% 2.58/0.99  inst_num_of_learning_restarts:          0
% 2.58/0.99  inst_num_moves_active_passive:          9
% 2.58/0.99  inst_lit_activity:                      0
% 2.58/0.99  inst_lit_activity_moves:                0
% 2.58/0.99  inst_num_tautologies:                   0
% 2.58/0.99  inst_num_prop_implied:                  0
% 2.58/0.99  inst_num_existing_simplified:           0
% 2.58/0.99  inst_num_eq_res_simplified:             0
% 2.58/0.99  inst_num_child_elim:                    0
% 2.58/0.99  inst_num_of_dismatching_blockings:      8
% 2.58/0.99  inst_num_of_non_proper_insts:           170
% 2.58/0.99  inst_num_of_duplicates:                 0
% 2.58/0.99  inst_inst_num_from_inst_to_res:         0
% 2.58/0.99  inst_dismatching_checking_time:         0.
% 2.58/0.99  
% 2.58/0.99  ------ Resolution
% 2.58/0.99  
% 2.58/0.99  res_num_of_clauses:                     0
% 2.58/0.99  res_num_in_passive:                     0
% 2.58/0.99  res_num_in_active:                      0
% 2.58/0.99  res_num_of_loops:                       94
% 2.58/0.99  res_forward_subset_subsumed:            13
% 2.58/0.99  res_backward_subset_subsumed:           0
% 2.58/0.99  res_forward_subsumed:                   0
% 2.58/0.99  res_backward_subsumed:                  1
% 2.58/0.99  res_forward_subsumption_resolution:     1
% 2.58/0.99  res_backward_subsumption_resolution:    0
% 2.58/0.99  res_clause_to_clause_subsumption:       47
% 2.58/0.99  res_orphan_elimination:                 0
% 2.58/0.99  res_tautology_del:                      9
% 2.58/0.99  res_num_eq_res_simplified:              1
% 2.58/0.99  res_num_sel_changes:                    0
% 2.58/0.99  res_moves_from_active_to_pass:          0
% 2.58/0.99  
% 2.58/0.99  ------ Superposition
% 2.58/0.99  
% 2.58/0.99  sup_time_total:                         0.
% 2.58/0.99  sup_time_generating:                    0.
% 2.58/0.99  sup_time_sim_full:                      0.
% 2.58/0.99  sup_time_sim_immed:                     0.
% 2.58/0.99  
% 2.58/0.99  sup_num_of_clauses:                     22
% 2.58/0.99  sup_num_in_active:                      17
% 2.58/0.99  sup_num_in_passive:                     5
% 2.58/0.99  sup_num_of_loops:                       25
% 2.58/0.99  sup_fw_superposition:                   20
% 2.58/0.99  sup_bw_superposition:                   9
% 2.58/0.99  sup_immediate_simplified:               7
% 2.58/0.99  sup_given_eliminated:                   0
% 2.58/0.99  comparisons_done:                       0
% 2.58/0.99  comparisons_avoided:                    0
% 2.58/0.99  
% 2.58/0.99  ------ Simplifications
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  sim_fw_subset_subsumed:                 2
% 2.58/0.99  sim_bw_subset_subsumed:                 0
% 2.58/0.99  sim_fw_subsumed:                        1
% 2.58/0.99  sim_bw_subsumed:                        0
% 2.58/0.99  sim_fw_subsumption_res:                 1
% 2.58/0.99  sim_bw_subsumption_res:                 0
% 2.58/0.99  sim_tautology_del:                      0
% 2.58/0.99  sim_eq_tautology_del:                   1
% 2.58/0.99  sim_eq_res_simp:                        0
% 2.58/0.99  sim_fw_demodulated:                     2
% 2.58/0.99  sim_bw_demodulated:                     8
% 2.58/0.99  sim_light_normalised:                   4
% 2.58/0.99  sim_joinable_taut:                      0
% 2.58/0.99  sim_joinable_simp:                      0
% 2.58/0.99  sim_ac_normalised:                      0
% 2.58/0.99  sim_smt_subsumption:                    0
% 2.58/0.99  
%------------------------------------------------------------------------------
