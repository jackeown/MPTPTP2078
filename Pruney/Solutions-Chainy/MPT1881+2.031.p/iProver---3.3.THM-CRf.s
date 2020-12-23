%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:16 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 614 expanded)
%              Number of clauses        :   99 ( 173 expanded)
%              Number of leaves         :   26 ( 137 expanded)
%              Depth                    :   22
%              Number of atoms          :  756 (3566 expanded)
%              Number of equality atoms :  139 ( 217 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK0(X0,X1,X2),X2)
            & r2_hidden(sK0(X0,X1,X2),X1)
            & m1_subset_1(sK0(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f43])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( v1_subset_1(sK4,u1_struct_0(X0))
          | ~ v3_tex_2(sK4,X0) )
        & ( ~ v1_subset_1(sK4,u1_struct_0(X0))
          | v3_tex_2(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK3))
            | ~ v3_tex_2(X1,sK3) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK3))
            | v3_tex_2(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v1_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( v1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_tex_2(sK4,sK3) )
    & ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
      | v3_tex_2(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v1_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f58,f60,f59])).

fof(f96,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f61])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f71,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f95,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK2(X0),X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).

fof(f87,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f78,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f94,plain,(
    v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f93,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f97,plain,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK1(X0,X1) != X1
        & r1_tarski(X1,sK1(X0,X1))
        & v2_tex_2(sK1(X0,X1),X0)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK1(X0,X1) != X1
                & r1_tarski(X1,sK1(X0,X1))
                & v2_tex_2(sK1(X0,X1),X0)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f51])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f98,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3679,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),X0)
    | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3975,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3679])).

cnf(c_7,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_17,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | X1 = X0
    | k2_subset_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_567,plain,
    ( ~ m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))
    | X0 = k2_subset_1(X0) ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_571,plain,
    ( X0 = k2_subset_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_567,c_1])).

cnf(c_3873,plain,
    ( u1_struct_0(sK3) = k2_subset_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_571])).

cnf(c_1771,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2312,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k2_subset_1(X2) ),
    inference(instantiation,[status(thm)],[c_1771])).

cnf(c_2569,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))
    | X0 != k2_subset_1(X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2312])).

cnf(c_3455,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 != k2_subset_1(u1_struct_0(sK3))
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2569])).

cnf(c_3872,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK3) != k2_subset_1(u1_struct_0(sK3))
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3455])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK0(X2,X0,X1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2416,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK0(X0,sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3548,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_2416])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X2,X0,X1),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2415,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3))
    | r2_hidden(sK0(X0,sK4,u1_struct_0(sK3)),sK4)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3544,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3))
    | r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),sK4)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_2415])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3421,plain,
    ( k2_subset_1(u1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1768,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2340,plain,
    ( k2_subset_1(u1_struct_0(sK3)) != X0
    | k2_subset_1(u1_struct_0(sK3)) = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1768])).

cnf(c_3314,plain,
    ( k2_subset_1(u1_struct_0(sK3)) != u1_struct_0(sK3)
    | k2_subset_1(u1_struct_0(sK3)) = sK4
    | sK4 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2340])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2084,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_8,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_472,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_9,c_8])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_769,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_472,c_33])).

cnf(c_770,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_769])).

cnf(c_2097,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2084,c_770])).

cnf(c_14,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_11,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_629,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | X2 != X1
    | X3 != X0
    | k2_pre_topc(X3,X2) = X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_11])).

cnf(c_630,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,X1) = X1 ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_27,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_702,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v1_tdlat_3(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | k2_pre_topc(X1,X0) = X0
    | k3_subset_1(u1_struct_0(X1),X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_630,c_27])).

cnf(c_703,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_702])).

cnf(c_16,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_719,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_703,c_16,c_2])).

cnf(c_34,negated_conjecture,
    ( v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_748,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_719,c_34])).

cnf(c_749,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | k2_pre_topc(sK3,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_748])).

cnf(c_753,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_749,c_33])).

cnf(c_2079,plain,
    ( k2_pre_topc(sK3,X0) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_2114,plain,
    ( k2_pre_topc(sK3,X0) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2079,c_770])).

cnf(c_2335,plain,
    ( k2_pre_topc(sK3,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_2097,c_2114])).

cnf(c_12,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_28,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_510,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_36])).

cnf(c_511,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_tex_2(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_511,c_35,c_34,c_33])).

cnf(c_516,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_515])).

cnf(c_29,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_486,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_36])).

cnf(c_487,plain,
    ( ~ v2_tex_2(X0,sK3)
    | v3_tex_2(X0,sK3)
    | ~ v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_491,plain,
    ( ~ v2_tex_2(X0,sK3)
    | v3_tex_2(X0,sK3)
    | ~ v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_487,c_35,c_33])).

cnf(c_526,plain,
    ( v3_tex_2(X0,sK3)
    | ~ v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_516,c_491])).

cnf(c_540,plain,
    ( v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(X2)
    | X0 != X1
    | k2_pre_topc(X2,X1) != k2_struct_0(X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_526])).

cnf(c_541,plain,
    ( v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | k2_pre_topc(sK3,X0) != k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_545,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_tex_2(X0,sK3)
    | k2_pre_topc(sK3,X0) != k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_541,c_33])).

cnf(c_546,plain,
    ( v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) != k2_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_545])).

cnf(c_2083,plain,
    ( k2_pre_topc(sK3,X0) != k2_struct_0(sK3)
    | v3_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_2144,plain,
    ( k2_pre_topc(sK3,X0) != k2_struct_0(sK3)
    | v3_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2083,c_770])).

cnf(c_2829,plain,
    ( k2_struct_0(sK3) != sK4
    | v3_tex_2(sK4,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2335,c_2144])).

cnf(c_31,negated_conjecture,
    ( v3_tex_2(sK4,sK3)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_274,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(prop_impl,[status(thm)],[c_31])).

cnf(c_589,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_274])).

cnf(c_590,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_592,plain,
    ( v3_tex_2(sK4,sK3)
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_590,c_32])).

cnf(c_2081,plain,
    ( u1_struct_0(sK3) = sK4
    | v3_tex_2(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_2103,plain,
    ( k2_struct_0(sK3) = sK4
    | v3_tex_2(sK4,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2081,c_770])).

cnf(c_3047,plain,
    ( v3_tex_2(sK4,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2829,c_2103,c_2097])).

cnf(c_1767,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2478,plain,
    ( k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1767])).

cnf(c_2264,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_23,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_783,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | X2 = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_784,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(X1,sK3)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_783])).

cnf(c_788,plain,
    ( ~ v3_tex_2(X1,sK3)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_784,c_35,c_34,c_33,c_511])).

cnf(c_789,plain,
    ( ~ v3_tex_2(X0,sK3)
    | ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_788])).

cnf(c_2261,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK4 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_789])).

cnf(c_2202,plain,
    ( v3_tex_2(sK4,sK3)
    | k2_struct_0(sK3) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2103])).

cnf(c_30,negated_conjecture,
    ( ~ v3_tex_2(sK4,sK3)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_276,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(prop_impl,[status(thm)],[c_30])).

cnf(c_577,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | u1_struct_0(sK3) != X0
    | k2_subset_1(X0) != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_276])).

cnf(c_578,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | k2_subset_1(u1_struct_0(sK3)) != sK4 ),
    inference(unflattening,[status(thm)],[c_577])).

cnf(c_2082,plain,
    ( k2_subset_1(u1_struct_0(sK3)) != sK4
    | v3_tex_2(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_578])).

cnf(c_2108,plain,
    ( k2_subset_1(k2_struct_0(sK3)) != sK4
    | v3_tex_2(sK4,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2082,c_770])).

cnf(c_2109,plain,
    ( k2_struct_0(sK3) != sK4
    | v3_tex_2(sK4,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2108,c_0])).

cnf(c_579,plain,
    ( k2_subset_1(u1_struct_0(sK3)) != sK4
    | v3_tex_2(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_578])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3975,c_3873,c_3872,c_3548,c_3544,c_3421,c_3314,c_3047,c_2478,c_2264,c_2261,c_2202,c_2109,c_579,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:06:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.68/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/0.98  
% 2.68/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.68/0.98  
% 2.68/0.98  ------  iProver source info
% 2.68/0.98  
% 2.68/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.68/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.68/0.98  git: non_committed_changes: false
% 2.68/0.98  git: last_make_outside_of_git: false
% 2.68/0.98  
% 2.68/0.98  ------ 
% 2.68/0.98  
% 2.68/0.98  ------ Input Options
% 2.68/0.98  
% 2.68/0.98  --out_options                           all
% 2.68/0.98  --tptp_safe_out                         true
% 2.68/0.98  --problem_path                          ""
% 2.68/0.98  --include_path                          ""
% 2.68/0.98  --clausifier                            res/vclausify_rel
% 2.68/0.98  --clausifier_options                    --mode clausify
% 2.68/0.98  --stdin                                 false
% 2.68/0.98  --stats_out                             all
% 2.68/0.98  
% 2.68/0.98  ------ General Options
% 2.68/0.98  
% 2.68/0.98  --fof                                   false
% 2.68/0.98  --time_out_real                         305.
% 2.68/0.98  --time_out_virtual                      -1.
% 2.68/0.98  --symbol_type_check                     false
% 2.68/0.98  --clausify_out                          false
% 2.68/0.98  --sig_cnt_out                           false
% 2.68/0.98  --trig_cnt_out                          false
% 2.68/0.98  --trig_cnt_out_tolerance                1.
% 2.68/0.98  --trig_cnt_out_sk_spl                   false
% 2.68/0.98  --abstr_cl_out                          false
% 2.68/0.98  
% 2.68/0.98  ------ Global Options
% 2.68/0.98  
% 2.68/0.98  --schedule                              default
% 2.68/0.98  --add_important_lit                     false
% 2.68/0.98  --prop_solver_per_cl                    1000
% 2.68/0.98  --min_unsat_core                        false
% 2.68/0.98  --soft_assumptions                      false
% 2.68/0.98  --soft_lemma_size                       3
% 2.68/0.98  --prop_impl_unit_size                   0
% 2.68/0.98  --prop_impl_unit                        []
% 2.68/0.98  --share_sel_clauses                     true
% 2.68/0.98  --reset_solvers                         false
% 2.68/0.98  --bc_imp_inh                            [conj_cone]
% 2.68/0.98  --conj_cone_tolerance                   3.
% 2.68/0.98  --extra_neg_conj                        none
% 2.68/0.98  --large_theory_mode                     true
% 2.68/0.98  --prolific_symb_bound                   200
% 2.68/0.98  --lt_threshold                          2000
% 2.68/0.98  --clause_weak_htbl                      true
% 2.68/0.98  --gc_record_bc_elim                     false
% 2.68/0.98  
% 2.68/0.98  ------ Preprocessing Options
% 2.68/0.98  
% 2.68/0.98  --preprocessing_flag                    true
% 2.68/0.98  --time_out_prep_mult                    0.1
% 2.68/0.98  --splitting_mode                        input
% 2.68/0.98  --splitting_grd                         true
% 2.68/0.98  --splitting_cvd                         false
% 2.68/0.98  --splitting_cvd_svl                     false
% 2.68/0.98  --splitting_nvd                         32
% 2.68/0.98  --sub_typing                            true
% 2.68/0.98  --prep_gs_sim                           true
% 2.68/0.98  --prep_unflatten                        true
% 2.68/0.98  --prep_res_sim                          true
% 2.68/0.98  --prep_upred                            true
% 2.68/0.98  --prep_sem_filter                       exhaustive
% 2.68/0.98  --prep_sem_filter_out                   false
% 2.68/0.98  --pred_elim                             true
% 2.68/0.98  --res_sim_input                         true
% 2.68/0.98  --eq_ax_congr_red                       true
% 2.68/0.98  --pure_diseq_elim                       true
% 2.68/0.98  --brand_transform                       false
% 2.68/0.98  --non_eq_to_eq                          false
% 2.68/0.98  --prep_def_merge                        true
% 2.68/0.98  --prep_def_merge_prop_impl              false
% 2.68/0.98  --prep_def_merge_mbd                    true
% 2.68/0.98  --prep_def_merge_tr_red                 false
% 2.68/0.98  --prep_def_merge_tr_cl                  false
% 2.68/0.98  --smt_preprocessing                     true
% 2.68/0.98  --smt_ac_axioms                         fast
% 2.68/0.98  --preprocessed_out                      false
% 2.68/0.98  --preprocessed_stats                    false
% 2.68/0.98  
% 2.68/0.98  ------ Abstraction refinement Options
% 2.68/0.98  
% 2.68/0.98  --abstr_ref                             []
% 2.68/0.98  --abstr_ref_prep                        false
% 2.68/0.98  --abstr_ref_until_sat                   false
% 2.68/0.98  --abstr_ref_sig_restrict                funpre
% 2.68/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.68/0.98  --abstr_ref_under                       []
% 2.68/0.98  
% 2.68/0.98  ------ SAT Options
% 2.68/0.98  
% 2.68/0.98  --sat_mode                              false
% 2.68/0.98  --sat_fm_restart_options                ""
% 2.68/0.98  --sat_gr_def                            false
% 2.68/0.98  --sat_epr_types                         true
% 2.68/0.98  --sat_non_cyclic_types                  false
% 2.68/0.98  --sat_finite_models                     false
% 2.68/0.98  --sat_fm_lemmas                         false
% 2.68/0.98  --sat_fm_prep                           false
% 2.68/0.98  --sat_fm_uc_incr                        true
% 2.68/0.98  --sat_out_model                         small
% 2.68/0.98  --sat_out_clauses                       false
% 2.68/0.98  
% 2.68/0.98  ------ QBF Options
% 2.68/0.98  
% 2.68/0.98  --qbf_mode                              false
% 2.68/0.98  --qbf_elim_univ                         false
% 2.68/0.98  --qbf_dom_inst                          none
% 2.68/0.98  --qbf_dom_pre_inst                      false
% 2.68/0.98  --qbf_sk_in                             false
% 2.68/0.98  --qbf_pred_elim                         true
% 2.68/0.98  --qbf_split                             512
% 2.68/0.98  
% 2.68/0.98  ------ BMC1 Options
% 2.68/0.98  
% 2.68/0.98  --bmc1_incremental                      false
% 2.68/0.98  --bmc1_axioms                           reachable_all
% 2.68/0.98  --bmc1_min_bound                        0
% 2.68/0.98  --bmc1_max_bound                        -1
% 2.68/0.98  --bmc1_max_bound_default                -1
% 2.68/0.98  --bmc1_symbol_reachability              true
% 2.68/0.98  --bmc1_property_lemmas                  false
% 2.68/0.98  --bmc1_k_induction                      false
% 2.68/0.98  --bmc1_non_equiv_states                 false
% 2.68/0.98  --bmc1_deadlock                         false
% 2.68/0.98  --bmc1_ucm                              false
% 2.68/0.98  --bmc1_add_unsat_core                   none
% 2.68/0.98  --bmc1_unsat_core_children              false
% 2.68/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.68/0.98  --bmc1_out_stat                         full
% 2.68/0.98  --bmc1_ground_init                      false
% 2.68/0.98  --bmc1_pre_inst_next_state              false
% 2.68/0.98  --bmc1_pre_inst_state                   false
% 2.68/0.98  --bmc1_pre_inst_reach_state             false
% 2.68/0.98  --bmc1_out_unsat_core                   false
% 2.68/0.98  --bmc1_aig_witness_out                  false
% 2.68/0.98  --bmc1_verbose                          false
% 2.68/0.98  --bmc1_dump_clauses_tptp                false
% 2.68/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.68/0.98  --bmc1_dump_file                        -
% 2.68/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.68/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.68/0.98  --bmc1_ucm_extend_mode                  1
% 2.68/0.98  --bmc1_ucm_init_mode                    2
% 2.68/0.98  --bmc1_ucm_cone_mode                    none
% 2.68/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.68/0.98  --bmc1_ucm_relax_model                  4
% 2.68/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.68/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.68/0.98  --bmc1_ucm_layered_model                none
% 2.68/0.98  --bmc1_ucm_max_lemma_size               10
% 2.68/0.98  
% 2.68/0.98  ------ AIG Options
% 2.68/0.98  
% 2.68/0.98  --aig_mode                              false
% 2.68/0.98  
% 2.68/0.98  ------ Instantiation Options
% 2.68/0.98  
% 2.68/0.98  --instantiation_flag                    true
% 2.68/0.98  --inst_sos_flag                         false
% 2.68/0.98  --inst_sos_phase                        true
% 2.68/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.68/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.68/0.98  --inst_lit_sel_side                     num_symb
% 2.68/0.98  --inst_solver_per_active                1400
% 2.68/0.98  --inst_solver_calls_frac                1.
% 2.68/0.98  --inst_passive_queue_type               priority_queues
% 2.68/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.68/0.98  --inst_passive_queues_freq              [25;2]
% 2.68/0.98  --inst_dismatching                      true
% 2.68/0.98  --inst_eager_unprocessed_to_passive     true
% 2.68/0.98  --inst_prop_sim_given                   true
% 2.68/0.98  --inst_prop_sim_new                     false
% 2.68/0.98  --inst_subs_new                         false
% 2.68/0.98  --inst_eq_res_simp                      false
% 2.68/0.98  --inst_subs_given                       false
% 2.68/0.98  --inst_orphan_elimination               true
% 2.68/0.98  --inst_learning_loop_flag               true
% 2.68/0.98  --inst_learning_start                   3000
% 2.68/0.98  --inst_learning_factor                  2
% 2.68/0.98  --inst_start_prop_sim_after_learn       3
% 2.68/0.98  --inst_sel_renew                        solver
% 2.68/0.98  --inst_lit_activity_flag                true
% 2.68/0.98  --inst_restr_to_given                   false
% 2.68/0.98  --inst_activity_threshold               500
% 2.68/0.98  --inst_out_proof                        true
% 2.68/0.98  
% 2.68/0.98  ------ Resolution Options
% 2.68/0.98  
% 2.68/0.98  --resolution_flag                       true
% 2.68/0.98  --res_lit_sel                           adaptive
% 2.68/0.98  --res_lit_sel_side                      none
% 2.68/0.98  --res_ordering                          kbo
% 2.68/0.98  --res_to_prop_solver                    active
% 2.68/0.98  --res_prop_simpl_new                    false
% 2.68/0.98  --res_prop_simpl_given                  true
% 2.68/0.98  --res_passive_queue_type                priority_queues
% 2.68/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.68/0.98  --res_passive_queues_freq               [15;5]
% 2.68/0.98  --res_forward_subs                      full
% 2.68/0.98  --res_backward_subs                     full
% 2.68/0.98  --res_forward_subs_resolution           true
% 2.68/0.98  --res_backward_subs_resolution          true
% 2.68/0.98  --res_orphan_elimination                true
% 2.68/0.98  --res_time_limit                        2.
% 2.68/0.98  --res_out_proof                         true
% 2.68/0.98  
% 2.68/0.98  ------ Superposition Options
% 2.68/0.98  
% 2.68/0.98  --superposition_flag                    true
% 2.68/0.98  --sup_passive_queue_type                priority_queues
% 2.68/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.68/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.68/0.98  --demod_completeness_check              fast
% 2.68/0.98  --demod_use_ground                      true
% 2.68/0.98  --sup_to_prop_solver                    passive
% 2.68/0.98  --sup_prop_simpl_new                    true
% 2.68/0.98  --sup_prop_simpl_given                  true
% 2.68/0.98  --sup_fun_splitting                     false
% 2.68/0.98  --sup_smt_interval                      50000
% 2.68/0.98  
% 2.68/0.98  ------ Superposition Simplification Setup
% 2.68/0.98  
% 2.68/0.98  --sup_indices_passive                   []
% 2.68/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.68/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.98  --sup_full_bw                           [BwDemod]
% 2.68/0.98  --sup_immed_triv                        [TrivRules]
% 2.68/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.68/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.98  --sup_immed_bw_main                     []
% 2.68/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.68/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/0.98  
% 2.68/0.98  ------ Combination Options
% 2.68/0.98  
% 2.68/0.98  --comb_res_mult                         3
% 2.68/0.98  --comb_sup_mult                         2
% 2.68/0.98  --comb_inst_mult                        10
% 2.68/0.98  
% 2.68/0.98  ------ Debug Options
% 2.68/0.98  
% 2.68/0.98  --dbg_backtrace                         false
% 2.68/0.98  --dbg_dump_prop_clauses                 false
% 2.68/0.98  --dbg_dump_prop_clauses_file            -
% 2.68/0.98  --dbg_out_stat                          false
% 2.68/0.98  ------ Parsing...
% 2.68/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.68/0.98  
% 2.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.68/0.98  
% 2.68/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.68/0.98  
% 2.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.68/0.98  ------ Proving...
% 2.68/0.98  ------ Problem Properties 
% 2.68/0.98  
% 2.68/0.98  
% 2.68/0.98  clauses                                 19
% 2.68/0.98  conjectures                             1
% 2.68/0.98  EPR                                     0
% 2.68/0.98  Horn                                    14
% 2.68/0.98  unary                                   5
% 2.68/0.98  binary                                  4
% 2.68/0.98  lits                                    48
% 2.68/0.98  lits eq                                 10
% 2.68/0.98  fd_pure                                 0
% 2.68/0.98  fd_pseudo                               0
% 2.68/0.98  fd_cond                                 0
% 2.68/0.98  fd_pseudo_cond                          1
% 2.68/0.98  AC symbols                              0
% 2.68/0.98  
% 2.68/0.98  ------ Schedule dynamic 5 is on 
% 2.68/0.98  
% 2.68/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.68/0.98  
% 2.68/0.98  
% 2.68/0.98  ------ 
% 2.68/0.98  Current options:
% 2.68/0.98  ------ 
% 2.68/0.98  
% 2.68/0.98  ------ Input Options
% 2.68/0.98  
% 2.68/0.98  --out_options                           all
% 2.68/0.98  --tptp_safe_out                         true
% 2.68/0.98  --problem_path                          ""
% 2.68/0.98  --include_path                          ""
% 2.68/0.98  --clausifier                            res/vclausify_rel
% 2.68/0.98  --clausifier_options                    --mode clausify
% 2.68/0.98  --stdin                                 false
% 2.68/0.98  --stats_out                             all
% 2.68/0.98  
% 2.68/0.98  ------ General Options
% 2.68/0.98  
% 2.68/0.98  --fof                                   false
% 2.68/0.98  --time_out_real                         305.
% 2.68/0.98  --time_out_virtual                      -1.
% 2.68/0.98  --symbol_type_check                     false
% 2.68/0.98  --clausify_out                          false
% 2.68/0.98  --sig_cnt_out                           false
% 2.68/0.98  --trig_cnt_out                          false
% 2.68/0.98  --trig_cnt_out_tolerance                1.
% 2.68/0.98  --trig_cnt_out_sk_spl                   false
% 2.68/0.98  --abstr_cl_out                          false
% 2.68/0.98  
% 2.68/0.98  ------ Global Options
% 2.68/0.98  
% 2.68/0.98  --schedule                              default
% 2.68/0.98  --add_important_lit                     false
% 2.68/0.98  --prop_solver_per_cl                    1000
% 2.68/0.98  --min_unsat_core                        false
% 2.68/0.98  --soft_assumptions                      false
% 2.68/0.98  --soft_lemma_size                       3
% 2.68/0.98  --prop_impl_unit_size                   0
% 2.68/0.98  --prop_impl_unit                        []
% 2.68/0.98  --share_sel_clauses                     true
% 2.68/0.98  --reset_solvers                         false
% 2.68/0.98  --bc_imp_inh                            [conj_cone]
% 2.68/0.98  --conj_cone_tolerance                   3.
% 2.68/0.98  --extra_neg_conj                        none
% 2.68/0.98  --large_theory_mode                     true
% 2.68/0.98  --prolific_symb_bound                   200
% 2.68/0.98  --lt_threshold                          2000
% 2.68/0.98  --clause_weak_htbl                      true
% 2.68/0.98  --gc_record_bc_elim                     false
% 2.68/0.98  
% 2.68/0.98  ------ Preprocessing Options
% 2.68/0.98  
% 2.68/0.98  --preprocessing_flag                    true
% 2.68/0.98  --time_out_prep_mult                    0.1
% 2.68/0.98  --splitting_mode                        input
% 2.68/0.98  --splitting_grd                         true
% 2.68/0.98  --splitting_cvd                         false
% 2.68/0.98  --splitting_cvd_svl                     false
% 2.68/0.98  --splitting_nvd                         32
% 2.68/0.98  --sub_typing                            true
% 2.68/0.98  --prep_gs_sim                           true
% 2.68/0.98  --prep_unflatten                        true
% 2.68/0.98  --prep_res_sim                          true
% 2.68/0.98  --prep_upred                            true
% 2.68/0.98  --prep_sem_filter                       exhaustive
% 2.68/0.98  --prep_sem_filter_out                   false
% 2.68/0.98  --pred_elim                             true
% 2.68/0.98  --res_sim_input                         true
% 2.68/0.98  --eq_ax_congr_red                       true
% 2.68/0.98  --pure_diseq_elim                       true
% 2.68/0.98  --brand_transform                       false
% 2.68/0.98  --non_eq_to_eq                          false
% 2.68/0.98  --prep_def_merge                        true
% 2.68/0.98  --prep_def_merge_prop_impl              false
% 2.68/0.98  --prep_def_merge_mbd                    true
% 2.68/0.98  --prep_def_merge_tr_red                 false
% 2.68/0.98  --prep_def_merge_tr_cl                  false
% 2.68/0.98  --smt_preprocessing                     true
% 2.68/0.98  --smt_ac_axioms                         fast
% 2.68/0.98  --preprocessed_out                      false
% 2.68/0.98  --preprocessed_stats                    false
% 2.68/0.98  
% 2.68/0.98  ------ Abstraction refinement Options
% 2.68/0.98  
% 2.68/0.98  --abstr_ref                             []
% 2.68/0.98  --abstr_ref_prep                        false
% 2.68/0.98  --abstr_ref_until_sat                   false
% 2.68/0.98  --abstr_ref_sig_restrict                funpre
% 2.68/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.68/0.98  --abstr_ref_under                       []
% 2.68/0.98  
% 2.68/0.98  ------ SAT Options
% 2.68/0.98  
% 2.68/0.98  --sat_mode                              false
% 2.68/0.98  --sat_fm_restart_options                ""
% 2.68/0.98  --sat_gr_def                            false
% 2.68/0.98  --sat_epr_types                         true
% 2.68/0.98  --sat_non_cyclic_types                  false
% 2.68/0.98  --sat_finite_models                     false
% 2.68/0.98  --sat_fm_lemmas                         false
% 2.68/0.98  --sat_fm_prep                           false
% 2.68/0.98  --sat_fm_uc_incr                        true
% 2.68/0.98  --sat_out_model                         small
% 2.68/0.98  --sat_out_clauses                       false
% 2.68/0.98  
% 2.68/0.98  ------ QBF Options
% 2.68/0.98  
% 2.68/0.98  --qbf_mode                              false
% 2.68/0.98  --qbf_elim_univ                         false
% 2.68/0.98  --qbf_dom_inst                          none
% 2.68/0.98  --qbf_dom_pre_inst                      false
% 2.68/0.98  --qbf_sk_in                             false
% 2.68/0.98  --qbf_pred_elim                         true
% 2.68/0.98  --qbf_split                             512
% 2.68/0.98  
% 2.68/0.98  ------ BMC1 Options
% 2.68/0.98  
% 2.68/0.98  --bmc1_incremental                      false
% 2.68/0.98  --bmc1_axioms                           reachable_all
% 2.68/0.98  --bmc1_min_bound                        0
% 2.68/0.98  --bmc1_max_bound                        -1
% 2.68/0.98  --bmc1_max_bound_default                -1
% 2.68/0.98  --bmc1_symbol_reachability              true
% 2.68/0.98  --bmc1_property_lemmas                  false
% 2.68/0.98  --bmc1_k_induction                      false
% 2.68/0.98  --bmc1_non_equiv_states                 false
% 2.68/0.98  --bmc1_deadlock                         false
% 2.68/0.98  --bmc1_ucm                              false
% 2.68/0.98  --bmc1_add_unsat_core                   none
% 2.68/0.98  --bmc1_unsat_core_children              false
% 2.68/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.68/0.98  --bmc1_out_stat                         full
% 2.68/0.98  --bmc1_ground_init                      false
% 2.68/0.98  --bmc1_pre_inst_next_state              false
% 2.68/0.98  --bmc1_pre_inst_state                   false
% 2.68/0.98  --bmc1_pre_inst_reach_state             false
% 2.68/0.98  --bmc1_out_unsat_core                   false
% 2.68/0.98  --bmc1_aig_witness_out                  false
% 2.68/0.98  --bmc1_verbose                          false
% 2.68/0.98  --bmc1_dump_clauses_tptp                false
% 2.68/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.68/0.98  --bmc1_dump_file                        -
% 2.68/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.68/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.68/0.98  --bmc1_ucm_extend_mode                  1
% 2.68/0.98  --bmc1_ucm_init_mode                    2
% 2.68/0.98  --bmc1_ucm_cone_mode                    none
% 2.68/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.68/0.98  --bmc1_ucm_relax_model                  4
% 2.68/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.68/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.68/0.98  --bmc1_ucm_layered_model                none
% 2.68/0.98  --bmc1_ucm_max_lemma_size               10
% 2.68/0.98  
% 2.68/0.98  ------ AIG Options
% 2.68/0.98  
% 2.68/0.98  --aig_mode                              false
% 2.68/0.98  
% 2.68/0.98  ------ Instantiation Options
% 2.68/0.98  
% 2.68/0.98  --instantiation_flag                    true
% 2.68/0.98  --inst_sos_flag                         false
% 2.68/0.98  --inst_sos_phase                        true
% 2.68/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.68/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.68/0.98  --inst_lit_sel_side                     none
% 2.68/0.98  --inst_solver_per_active                1400
% 2.68/0.98  --inst_solver_calls_frac                1.
% 2.68/0.98  --inst_passive_queue_type               priority_queues
% 2.68/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.68/0.98  --inst_passive_queues_freq              [25;2]
% 2.68/0.98  --inst_dismatching                      true
% 2.68/0.98  --inst_eager_unprocessed_to_passive     true
% 2.68/0.98  --inst_prop_sim_given                   true
% 2.68/0.98  --inst_prop_sim_new                     false
% 2.68/0.98  --inst_subs_new                         false
% 2.68/0.98  --inst_eq_res_simp                      false
% 2.68/0.98  --inst_subs_given                       false
% 2.68/0.98  --inst_orphan_elimination               true
% 2.68/0.98  --inst_learning_loop_flag               true
% 2.68/0.98  --inst_learning_start                   3000
% 2.68/0.98  --inst_learning_factor                  2
% 2.68/0.98  --inst_start_prop_sim_after_learn       3
% 2.68/0.98  --inst_sel_renew                        solver
% 2.68/0.98  --inst_lit_activity_flag                true
% 2.68/0.98  --inst_restr_to_given                   false
% 2.68/0.98  --inst_activity_threshold               500
% 2.68/0.98  --inst_out_proof                        true
% 2.68/0.98  
% 2.68/0.98  ------ Resolution Options
% 2.68/0.98  
% 2.68/0.98  --resolution_flag                       false
% 2.68/0.98  --res_lit_sel                           adaptive
% 2.68/0.98  --res_lit_sel_side                      none
% 2.68/0.98  --res_ordering                          kbo
% 2.68/0.98  --res_to_prop_solver                    active
% 2.68/0.98  --res_prop_simpl_new                    false
% 2.68/0.98  --res_prop_simpl_given                  true
% 2.68/0.98  --res_passive_queue_type                priority_queues
% 2.68/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.68/0.98  --res_passive_queues_freq               [15;5]
% 2.68/0.98  --res_forward_subs                      full
% 2.68/0.98  --res_backward_subs                     full
% 2.68/0.98  --res_forward_subs_resolution           true
% 2.68/0.98  --res_backward_subs_resolution          true
% 2.68/0.98  --res_orphan_elimination                true
% 2.68/0.98  --res_time_limit                        2.
% 2.68/0.98  --res_out_proof                         true
% 2.68/0.98  
% 2.68/0.98  ------ Superposition Options
% 2.68/0.98  
% 2.68/0.98  --superposition_flag                    true
% 2.68/0.98  --sup_passive_queue_type                priority_queues
% 2.68/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.68/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.68/0.98  --demod_completeness_check              fast
% 2.68/0.98  --demod_use_ground                      true
% 2.68/0.98  --sup_to_prop_solver                    passive
% 2.68/0.98  --sup_prop_simpl_new                    true
% 2.68/0.98  --sup_prop_simpl_given                  true
% 2.68/0.98  --sup_fun_splitting                     false
% 2.68/0.98  --sup_smt_interval                      50000
% 2.68/0.98  
% 2.68/0.98  ------ Superposition Simplification Setup
% 2.68/0.98  
% 2.68/0.98  --sup_indices_passive                   []
% 2.68/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.68/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.98  --sup_full_bw                           [BwDemod]
% 2.68/0.98  --sup_immed_triv                        [TrivRules]
% 2.68/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.68/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.98  --sup_immed_bw_main                     []
% 2.68/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.68/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/0.98  
% 2.68/0.98  ------ Combination Options
% 2.68/0.98  
% 2.68/0.98  --comb_res_mult                         3
% 2.68/0.98  --comb_sup_mult                         2
% 2.68/0.98  --comb_inst_mult                        10
% 2.68/0.98  
% 2.68/0.98  ------ Debug Options
% 2.68/0.98  
% 2.68/0.98  --dbg_backtrace                         false
% 2.68/0.98  --dbg_dump_prop_clauses                 false
% 2.68/0.98  --dbg_dump_prop_clauses_file            -
% 2.68/0.98  --dbg_out_stat                          false
% 2.68/0.98  
% 2.68/0.98  
% 2.68/0.98  
% 2.68/0.98  
% 2.68/0.98  ------ Proving...
% 2.68/0.98  
% 2.68/0.98  
% 2.68/0.98  % SZS status Theorem for theBenchmark.p
% 2.68/0.98  
% 2.68/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.68/0.98  
% 2.68/0.98  fof(f4,axiom,(
% 2.68/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f21,plain,(
% 2.68/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.68/0.98    inference(ennf_transformation,[],[f4])).
% 2.68/0.98  
% 2.68/0.98  fof(f65,plain,(
% 2.68/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.68/0.98    inference(cnf_transformation,[],[f21])).
% 2.68/0.98  
% 2.68/0.98  fof(f6,axiom,(
% 2.68/0.98    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 2.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f69,plain,(
% 2.68/0.98    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f6])).
% 2.68/0.98  
% 2.68/0.98  fof(f13,axiom,(
% 2.68/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f32,plain,(
% 2.68/0.98    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.68/0.98    inference(ennf_transformation,[],[f13])).
% 2.68/0.98  
% 2.68/0.98  fof(f47,plain,(
% 2.68/0.98    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.68/0.98    inference(nnf_transformation,[],[f32])).
% 2.68/0.98  
% 2.68/0.98  fof(f80,plain,(
% 2.68/0.98    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.68/0.98    inference(cnf_transformation,[],[f47])).
% 2.68/0.98  
% 2.68/0.98  fof(f2,axiom,(
% 2.68/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f63,plain,(
% 2.68/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.68/0.98    inference(cnf_transformation,[],[f2])).
% 2.68/0.98  
% 2.68/0.98  fof(f5,axiom,(
% 2.68/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 2.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f22,plain,(
% 2.68/0.98    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.68/0.98    inference(ennf_transformation,[],[f5])).
% 2.68/0.98  
% 2.68/0.98  fof(f23,plain,(
% 2.68/0.98    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.68/0.98    inference(flattening,[],[f22])).
% 2.68/0.98  
% 2.68/0.98  fof(f43,plain,(
% 2.68/0.98    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)))),
% 2.68/0.98    introduced(choice_axiom,[])).
% 2.68/0.98  
% 2.68/0.98  fof(f44,plain,(
% 2.68/0.98    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f43])).
% 2.68/0.98  
% 2.68/0.98  fof(f68,plain,(
% 2.68/0.98    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.68/0.98    inference(cnf_transformation,[],[f44])).
% 2.68/0.98  
% 2.68/0.98  fof(f67,plain,(
% 2.68/0.98    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.68/0.98    inference(cnf_transformation,[],[f44])).
% 2.68/0.98  
% 2.68/0.98  fof(f1,axiom,(
% 2.68/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 2.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f62,plain,(
% 2.68/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.68/0.98    inference(cnf_transformation,[],[f1])).
% 2.68/0.98  
% 2.68/0.98  fof(f18,conjecture,(
% 2.68/0.98    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 2.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f19,negated_conjecture,(
% 2.68/0.98    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 2.68/0.98    inference(negated_conjecture,[],[f18])).
% 2.68/0.98  
% 2.68/0.98  fof(f41,plain,(
% 2.68/0.98    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.68/0.98    inference(ennf_transformation,[],[f19])).
% 2.68/0.98  
% 2.68/0.98  fof(f42,plain,(
% 2.68/0.98    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.68/0.98    inference(flattening,[],[f41])).
% 2.68/0.98  
% 2.68/0.98  fof(f57,plain,(
% 2.68/0.98    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.68/0.98    inference(nnf_transformation,[],[f42])).
% 2.68/0.98  
% 2.68/0.98  fof(f58,plain,(
% 2.68/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.68/0.98    inference(flattening,[],[f57])).
% 2.68/0.98  
% 2.68/0.98  fof(f60,plain,(
% 2.68/0.98    ( ! [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_subset_1(sK4,u1_struct_0(X0)) | ~v3_tex_2(sK4,X0)) & (~v1_subset_1(sK4,u1_struct_0(X0)) | v3_tex_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.68/0.98    introduced(choice_axiom,[])).
% 2.68/0.98  
% 2.68/0.98  fof(f59,plain,(
% 2.68/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK3)) | ~v3_tex_2(X1,sK3)) & (~v1_subset_1(X1,u1_struct_0(sK3)) | v3_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v1_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.68/0.98    introduced(choice_axiom,[])).
% 2.68/0.98  
% 2.68/0.98  fof(f61,plain,(
% 2.68/0.98    ((v1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_tex_2(sK4,sK3)) & (~v1_subset_1(sK4,u1_struct_0(sK3)) | v3_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v1_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f58,f60,f59])).
% 2.68/0.98  
% 2.68/0.98  fof(f96,plain,(
% 2.68/0.98    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.68/0.98    inference(cnf_transformation,[],[f61])).
% 2.68/0.98  
% 2.68/0.98  fof(f8,axiom,(
% 2.68/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f25,plain,(
% 2.68/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.68/0.98    inference(ennf_transformation,[],[f8])).
% 2.68/0.98  
% 2.68/0.98  fof(f71,plain,(
% 2.68/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f25])).
% 2.68/0.98  
% 2.68/0.98  fof(f7,axiom,(
% 2.68/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f24,plain,(
% 2.68/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.68/0.98    inference(ennf_transformation,[],[f7])).
% 2.68/0.98  
% 2.68/0.98  fof(f70,plain,(
% 2.68/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f24])).
% 2.68/0.98  
% 2.68/0.98  fof(f95,plain,(
% 2.68/0.98    l1_pre_topc(sK3)),
% 2.68/0.98    inference(cnf_transformation,[],[f61])).
% 2.68/0.98  
% 2.68/0.98  fof(f11,axiom,(
% 2.68/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f29,plain,(
% 2.68/0.98    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.68/0.98    inference(ennf_transformation,[],[f11])).
% 2.68/0.98  
% 2.68/0.98  fof(f46,plain,(
% 2.68/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.68/0.98    inference(nnf_transformation,[],[f29])).
% 2.68/0.98  
% 2.68/0.98  fof(f77,plain,(
% 2.68/0.98    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f46])).
% 2.68/0.98  
% 2.68/0.98  fof(f9,axiom,(
% 2.68/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f26,plain,(
% 2.68/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.68/0.98    inference(ennf_transformation,[],[f9])).
% 2.68/0.98  
% 2.68/0.98  fof(f27,plain,(
% 2.68/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.68/0.98    inference(flattening,[],[f26])).
% 2.68/0.98  
% 2.68/0.98  fof(f72,plain,(
% 2.68/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f27])).
% 2.68/0.98  
% 2.68/0.98  fof(f15,axiom,(
% 2.68/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 2.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f35,plain,(
% 2.68/0.98    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.68/0.98    inference(ennf_transformation,[],[f15])).
% 2.68/0.98  
% 2.68/0.98  fof(f36,plain,(
% 2.68/0.98    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.68/0.98    inference(flattening,[],[f35])).
% 2.68/0.98  
% 2.68/0.98  fof(f53,plain,(
% 2.68/0.98    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.68/0.98    inference(nnf_transformation,[],[f36])).
% 2.68/0.98  
% 2.68/0.98  fof(f54,plain,(
% 2.68/0.98    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.68/0.98    inference(rectify,[],[f53])).
% 2.68/0.98  
% 2.68/0.98  fof(f55,plain,(
% 2.68/0.98    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.68/0.98    introduced(choice_axiom,[])).
% 2.68/0.98  
% 2.68/0.98  fof(f56,plain,(
% 2.68/0.98    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).
% 2.68/0.98  
% 2.68/0.98  fof(f87,plain,(
% 2.68/0.98    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f56])).
% 2.68/0.98  
% 2.68/0.98  fof(f12,axiom,(
% 2.68/0.98    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 2.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f30,plain,(
% 2.68/0.98    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 2.68/0.98    inference(ennf_transformation,[],[f12])).
% 2.68/0.98  
% 2.68/0.98  fof(f31,plain,(
% 2.68/0.98    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 2.68/0.98    inference(flattening,[],[f30])).
% 2.68/0.98  
% 2.68/0.98  fof(f78,plain,(
% 2.68/0.98    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f31])).
% 2.68/0.98  
% 2.68/0.98  fof(f3,axiom,(
% 2.68/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f20,plain,(
% 2.68/0.98    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.68/0.98    inference(ennf_transformation,[],[f3])).
% 2.68/0.98  
% 2.68/0.98  fof(f64,plain,(
% 2.68/0.98    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.68/0.98    inference(cnf_transformation,[],[f20])).
% 2.68/0.98  
% 2.68/0.98  fof(f94,plain,(
% 2.68/0.98    v1_tdlat_3(sK3)),
% 2.68/0.98    inference(cnf_transformation,[],[f61])).
% 2.68/0.98  
% 2.68/0.98  fof(f10,axiom,(
% 2.68/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f28,plain,(
% 2.68/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.68/0.98    inference(ennf_transformation,[],[f10])).
% 2.68/0.98  
% 2.68/0.98  fof(f45,plain,(
% 2.68/0.98    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.68/0.98    inference(nnf_transformation,[],[f28])).
% 2.68/0.98  
% 2.68/0.98  fof(f75,plain,(
% 2.68/0.98    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f45])).
% 2.68/0.98  
% 2.68/0.98  fof(f16,axiom,(
% 2.68/0.98    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 2.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f37,plain,(
% 2.68/0.98    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.68/0.98    inference(ennf_transformation,[],[f16])).
% 2.68/0.98  
% 2.68/0.98  fof(f38,plain,(
% 2.68/0.98    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.68/0.98    inference(flattening,[],[f37])).
% 2.68/0.98  
% 2.68/0.98  fof(f90,plain,(
% 2.68/0.98    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f38])).
% 2.68/0.98  
% 2.68/0.98  fof(f92,plain,(
% 2.68/0.98    ~v2_struct_0(sK3)),
% 2.68/0.98    inference(cnf_transformation,[],[f61])).
% 2.68/0.98  
% 2.68/0.98  fof(f93,plain,(
% 2.68/0.98    v2_pre_topc(sK3)),
% 2.68/0.98    inference(cnf_transformation,[],[f61])).
% 2.68/0.98  
% 2.68/0.98  fof(f17,axiom,(
% 2.68/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 2.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f39,plain,(
% 2.68/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.68/0.98    inference(ennf_transformation,[],[f17])).
% 2.68/0.98  
% 2.68/0.98  fof(f40,plain,(
% 2.68/0.98    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.68/0.98    inference(flattening,[],[f39])).
% 2.68/0.98  
% 2.68/0.98  fof(f91,plain,(
% 2.68/0.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f40])).
% 2.68/0.98  
% 2.68/0.98  fof(f97,plain,(
% 2.68/0.98    ~v1_subset_1(sK4,u1_struct_0(sK3)) | v3_tex_2(sK4,sK3)),
% 2.68/0.98    inference(cnf_transformation,[],[f61])).
% 2.68/0.98  
% 2.68/0.98  fof(f14,axiom,(
% 2.68/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 2.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f33,plain,(
% 2.68/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.68/0.98    inference(ennf_transformation,[],[f14])).
% 2.68/0.98  
% 2.68/0.98  fof(f34,plain,(
% 2.68/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.68/0.98    inference(flattening,[],[f33])).
% 2.68/0.98  
% 2.68/0.98  fof(f48,plain,(
% 2.68/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.68/0.98    inference(nnf_transformation,[],[f34])).
% 2.68/0.98  
% 2.68/0.98  fof(f49,plain,(
% 2.68/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.68/0.98    inference(flattening,[],[f48])).
% 2.68/0.98  
% 2.68/0.98  fof(f50,plain,(
% 2.68/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.68/0.98    inference(rectify,[],[f49])).
% 2.68/0.98  
% 2.68/0.98  fof(f51,plain,(
% 2.68/0.98    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.68/0.98    introduced(choice_axiom,[])).
% 2.68/0.98  
% 2.68/0.98  fof(f52,plain,(
% 2.68/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f51])).
% 2.68/0.98  
% 2.68/0.98  fof(f82,plain,(
% 2.68/0.98    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f52])).
% 2.68/0.98  
% 2.68/0.98  fof(f98,plain,(
% 2.68/0.98    v1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_tex_2(sK4,sK3)),
% 2.68/0.98    inference(cnf_transformation,[],[f61])).
% 2.68/0.98  
% 2.68/0.98  cnf(c_3,plain,
% 2.68/0.98      ( ~ r2_hidden(X0,X1)
% 2.68/0.98      | r2_hidden(X0,X2)
% 2.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.68/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_3679,plain,
% 2.68/0.98      ( r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),X0)
% 2.68/0.98      | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),sK4)
% 2.68/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) ),
% 2.68/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_3975,plain,
% 2.68/0.98      ( r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.68/0.98      | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),sK4)
% 2.68/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.68/0.98      inference(instantiation,[status(thm)],[c_3679]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_7,plain,
% 2.68/0.98      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 2.68/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_17,plain,
% 2.68/0.98      ( v1_subset_1(X0,X1)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.68/0.98      | X0 = X1 ),
% 2.68/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_566,plain,
% 2.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.68/0.98      | X1 != X2
% 2.68/0.98      | X1 = X0
% 2.68/0.98      | k2_subset_1(X2) != X0 ),
% 2.68/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_567,plain,
% 2.68/0.98      ( ~ m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))
% 2.68/0.98      | X0 = k2_subset_1(X0) ),
% 2.68/0.98      inference(unflattening,[status(thm)],[c_566]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_1,plain,
% 2.68/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.68/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_571,plain,
% 2.68/0.98      ( X0 = k2_subset_1(X0) ),
% 2.68/0.98      inference(global_propositional_subsumption,
% 2.68/0.98                [status(thm)],
% 2.68/0.98                [c_567,c_1]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_3873,plain,
% 2.68/0.98      ( u1_struct_0(sK3) = k2_subset_1(u1_struct_0(sK3)) ),
% 2.68/0.98      inference(instantiation,[status(thm)],[c_571]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_1771,plain,
% 2.68/0.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.68/0.98      theory(equality) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2312,plain,
% 2.68/0.98      ( m1_subset_1(X0,X1)
% 2.68/0.98      | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
% 2.68/0.98      | X1 != k1_zfmisc_1(X2)
% 2.68/0.98      | X0 != k2_subset_1(X2) ),
% 2.68/0.98      inference(instantiation,[status(thm)],[c_1771]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2569,plain,
% 2.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.68/0.98      | ~ m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))
% 2.68/0.98      | X0 != k2_subset_1(X1)
% 2.68/0.98      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 2.68/0.98      inference(instantiation,[status(thm)],[c_2312]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_3455,plain,
% 2.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | X0 != k2_subset_1(u1_struct_0(sK3))
% 2.68/0.98      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 2.68/0.98      inference(instantiation,[status(thm)],[c_2569]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_3872,plain,
% 2.68/0.98      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | u1_struct_0(sK3) != k2_subset_1(u1_struct_0(sK3))
% 2.68/0.98      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 2.68/0.98      inference(instantiation,[status(thm)],[c_3455]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_4,plain,
% 2.68/0.98      ( r1_tarski(X0,X1)
% 2.68/0.98      | ~ r2_hidden(sK0(X2,X0,X1),X1)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 2.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.68/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2416,plain,
% 2.68/0.98      ( r1_tarski(sK4,u1_struct_0(sK3))
% 2.68/0.98      | ~ r2_hidden(sK0(X0,sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.68/0.98      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0))
% 2.68/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) ),
% 2.68/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_3548,plain,
% 2.68/0.98      ( r1_tarski(sK4,u1_struct_0(sK3))
% 2.68/0.98      | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.68/0.98      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.68/0.98      inference(instantiation,[status(thm)],[c_2416]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_5,plain,
% 2.68/0.98      ( r1_tarski(X0,X1)
% 2.68/0.98      | r2_hidden(sK0(X2,X0,X1),X0)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 2.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.68/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2415,plain,
% 2.68/0.98      ( r1_tarski(sK4,u1_struct_0(sK3))
% 2.68/0.98      | r2_hidden(sK0(X0,sK4,u1_struct_0(sK3)),sK4)
% 2.68/0.98      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0))
% 2.68/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) ),
% 2.68/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_3544,plain,
% 2.68/0.98      ( r1_tarski(sK4,u1_struct_0(sK3))
% 2.68/0.98      | r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),sK4)
% 2.68/0.98      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.68/0.98      inference(instantiation,[status(thm)],[c_2415]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_0,plain,
% 2.68/0.98      ( k2_subset_1(X0) = X0 ),
% 2.68/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_3421,plain,
% 2.68/0.98      ( k2_subset_1(u1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 2.68/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_1768,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2340,plain,
% 2.68/0.98      ( k2_subset_1(u1_struct_0(sK3)) != X0
% 2.68/0.98      | k2_subset_1(u1_struct_0(sK3)) = sK4
% 2.68/0.98      | sK4 != X0 ),
% 2.68/0.98      inference(instantiation,[status(thm)],[c_1768]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_3314,plain,
% 2.68/0.98      ( k2_subset_1(u1_struct_0(sK3)) != u1_struct_0(sK3)
% 2.68/0.98      | k2_subset_1(u1_struct_0(sK3)) = sK4
% 2.68/0.98      | sK4 != u1_struct_0(sK3) ),
% 2.68/0.98      inference(instantiation,[status(thm)],[c_2340]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_32,negated_conjecture,
% 2.68/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.68/0.98      inference(cnf_transformation,[],[f96]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2084,plain,
% 2.68/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.68/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_9,plain,
% 2.68/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.68/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_8,plain,
% 2.68/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.68/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_472,plain,
% 2.68/0.98      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.68/0.98      inference(resolution,[status(thm)],[c_9,c_8]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_33,negated_conjecture,
% 2.68/0.98      ( l1_pre_topc(sK3) ),
% 2.68/0.98      inference(cnf_transformation,[],[f95]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_769,plain,
% 2.68/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 2.68/0.98      inference(resolution_lifted,[status(thm)],[c_472,c_33]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_770,plain,
% 2.68/0.98      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 2.68/0.98      inference(unflattening,[status(thm)],[c_769]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2097,plain,
% 2.68/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 2.68/0.98      inference(light_normalisation,[status(thm)],[c_2084,c_770]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_14,plain,
% 2.68/0.98      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 2.68/0.98      | v4_pre_topc(X1,X0)
% 2.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.68/0.98      | ~ l1_pre_topc(X0) ),
% 2.68/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_11,plain,
% 2.68/0.98      ( ~ v4_pre_topc(X0,X1)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.68/0.98      | ~ l1_pre_topc(X1)
% 2.68/0.98      | k2_pre_topc(X1,X0) = X0 ),
% 2.68/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_629,plain,
% 2.68/0.98      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 2.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.68/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.68/0.98      | ~ l1_pre_topc(X0)
% 2.68/0.98      | ~ l1_pre_topc(X3)
% 2.68/0.98      | X2 != X1
% 2.68/0.98      | X3 != X0
% 2.68/0.98      | k2_pre_topc(X3,X2) = X2 ),
% 2.68/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_11]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_630,plain,
% 2.68/0.98      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 2.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.68/0.98      | ~ l1_pre_topc(X0)
% 2.68/0.98      | k2_pre_topc(X0,X1) = X1 ),
% 2.68/0.98      inference(unflattening,[status(thm)],[c_629]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_27,plain,
% 2.68/0.98      ( v3_pre_topc(X0,X1)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.68/0.98      | ~ v1_tdlat_3(X1)
% 2.68/0.98      | ~ v2_pre_topc(X1)
% 2.68/0.98      | ~ l1_pre_topc(X1) ),
% 2.68/0.98      inference(cnf_transformation,[],[f87]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_702,plain,
% 2.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.68/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.68/0.98      | ~ v1_tdlat_3(X3)
% 2.68/0.98      | ~ v2_pre_topc(X3)
% 2.68/0.98      | ~ l1_pre_topc(X1)
% 2.68/0.98      | ~ l1_pre_topc(X3)
% 2.68/0.98      | X3 != X1
% 2.68/0.98      | k2_pre_topc(X1,X0) = X0
% 2.68/0.98      | k3_subset_1(u1_struct_0(X1),X0) != X2 ),
% 2.68/0.98      inference(resolution_lifted,[status(thm)],[c_630,c_27]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_703,plain,
% 2.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.68/0.98      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.68/0.98      | ~ v1_tdlat_3(X1)
% 2.68/0.98      | ~ v2_pre_topc(X1)
% 2.68/0.98      | ~ l1_pre_topc(X1)
% 2.68/0.98      | k2_pre_topc(X1,X0) = X0 ),
% 2.68/0.98      inference(unflattening,[status(thm)],[c_702]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_16,plain,
% 2.68/0.98      ( ~ v1_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 2.68/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2,plain,
% 2.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.68/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.68/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_719,plain,
% 2.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.68/0.98      | ~ v1_tdlat_3(X1)
% 2.68/0.98      | ~ l1_pre_topc(X1)
% 2.68/0.98      | k2_pre_topc(X1,X0) = X0 ),
% 2.68/0.98      inference(forward_subsumption_resolution,
% 2.68/0.98                [status(thm)],
% 2.68/0.98                [c_703,c_16,c_2]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_34,negated_conjecture,
% 2.68/0.98      ( v1_tdlat_3(sK3) ),
% 2.68/0.98      inference(cnf_transformation,[],[f94]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_748,plain,
% 2.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.68/0.98      | ~ l1_pre_topc(X1)
% 2.68/0.98      | k2_pre_topc(X1,X0) = X0
% 2.68/0.98      | sK3 != X1 ),
% 2.68/0.98      inference(resolution_lifted,[status(thm)],[c_719,c_34]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_749,plain,
% 2.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | ~ l1_pre_topc(sK3)
% 2.68/0.98      | k2_pre_topc(sK3,X0) = X0 ),
% 2.68/0.98      inference(unflattening,[status(thm)],[c_748]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_753,plain,
% 2.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | k2_pre_topc(sK3,X0) = X0 ),
% 2.68/0.98      inference(global_propositional_subsumption,
% 2.68/0.98                [status(thm)],
% 2.68/0.98                [c_749,c_33]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2079,plain,
% 2.68/0.98      ( k2_pre_topc(sK3,X0) = X0
% 2.68/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.68/0.98      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2114,plain,
% 2.68/0.98      ( k2_pre_topc(sK3,X0) = X0
% 2.68/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.68/0.98      inference(light_normalisation,[status(thm)],[c_2079,c_770]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2335,plain,
% 2.68/0.98      ( k2_pre_topc(sK3,sK4) = sK4 ),
% 2.68/0.98      inference(superposition,[status(thm)],[c_2097,c_2114]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_12,plain,
% 2.68/0.98      ( v1_tops_1(X0,X1)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.68/0.98      | ~ l1_pre_topc(X1)
% 2.68/0.98      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 2.68/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_28,plain,
% 2.68/0.98      ( v2_tex_2(X0,X1)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.68/0.98      | v2_struct_0(X1)
% 2.68/0.98      | ~ v1_tdlat_3(X1)
% 2.68/0.98      | ~ v2_pre_topc(X1)
% 2.68/0.98      | ~ l1_pre_topc(X1) ),
% 2.68/0.98      inference(cnf_transformation,[],[f90]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_36,negated_conjecture,
% 2.68/0.98      ( ~ v2_struct_0(sK3) ),
% 2.68/0.98      inference(cnf_transformation,[],[f92]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_510,plain,
% 2.68/0.98      ( v2_tex_2(X0,X1)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.68/0.98      | ~ v1_tdlat_3(X1)
% 2.68/0.98      | ~ v2_pre_topc(X1)
% 2.68/0.98      | ~ l1_pre_topc(X1)
% 2.68/0.98      | sK3 != X1 ),
% 2.68/0.98      inference(resolution_lifted,[status(thm)],[c_28,c_36]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_511,plain,
% 2.68/0.98      ( v2_tex_2(X0,sK3)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | ~ v1_tdlat_3(sK3)
% 2.68/0.98      | ~ v2_pre_topc(sK3)
% 2.68/0.98      | ~ l1_pre_topc(sK3) ),
% 2.68/0.98      inference(unflattening,[status(thm)],[c_510]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_35,negated_conjecture,
% 2.68/0.98      ( v2_pre_topc(sK3) ),
% 2.68/0.98      inference(cnf_transformation,[],[f93]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_515,plain,
% 2.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | v2_tex_2(X0,sK3) ),
% 2.68/0.98      inference(global_propositional_subsumption,
% 2.68/0.98                [status(thm)],
% 2.68/0.98                [c_511,c_35,c_34,c_33]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_516,plain,
% 2.68/0.98      ( v2_tex_2(X0,sK3)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.68/0.98      inference(renaming,[status(thm)],[c_515]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_29,plain,
% 2.68/0.98      ( ~ v2_tex_2(X0,X1)
% 2.68/0.98      | v3_tex_2(X0,X1)
% 2.68/0.98      | ~ v1_tops_1(X0,X1)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.68/0.98      | v2_struct_0(X1)
% 2.68/0.98      | ~ v2_pre_topc(X1)
% 2.68/0.98      | ~ l1_pre_topc(X1) ),
% 2.68/0.98      inference(cnf_transformation,[],[f91]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_486,plain,
% 2.68/0.98      ( ~ v2_tex_2(X0,X1)
% 2.68/0.98      | v3_tex_2(X0,X1)
% 2.68/0.98      | ~ v1_tops_1(X0,X1)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.68/0.98      | ~ v2_pre_topc(X1)
% 2.68/0.98      | ~ l1_pre_topc(X1)
% 2.68/0.98      | sK3 != X1 ),
% 2.68/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_36]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_487,plain,
% 2.68/0.98      ( ~ v2_tex_2(X0,sK3)
% 2.68/0.98      | v3_tex_2(X0,sK3)
% 2.68/0.98      | ~ v1_tops_1(X0,sK3)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | ~ v2_pre_topc(sK3)
% 2.68/0.98      | ~ l1_pre_topc(sK3) ),
% 2.68/0.98      inference(unflattening,[status(thm)],[c_486]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_491,plain,
% 2.68/0.98      ( ~ v2_tex_2(X0,sK3)
% 2.68/0.98      | v3_tex_2(X0,sK3)
% 2.68/0.98      | ~ v1_tops_1(X0,sK3)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.68/0.98      inference(global_propositional_subsumption,
% 2.68/0.98                [status(thm)],
% 2.68/0.98                [c_487,c_35,c_33]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_526,plain,
% 2.68/0.98      ( v3_tex_2(X0,sK3)
% 2.68/0.98      | ~ v1_tops_1(X0,sK3)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.68/0.98      inference(backward_subsumption_resolution,
% 2.68/0.98                [status(thm)],
% 2.68/0.98                [c_516,c_491]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_540,plain,
% 2.68/0.98      ( v3_tex_2(X0,sK3)
% 2.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | ~ l1_pre_topc(X2)
% 2.68/0.98      | X0 != X1
% 2.68/0.98      | k2_pre_topc(X2,X1) != k2_struct_0(X2)
% 2.68/0.98      | sK3 != X2 ),
% 2.68/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_526]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_541,plain,
% 2.68/0.98      ( v3_tex_2(X0,sK3)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | ~ l1_pre_topc(sK3)
% 2.68/0.98      | k2_pre_topc(sK3,X0) != k2_struct_0(sK3) ),
% 2.68/0.98      inference(unflattening,[status(thm)],[c_540]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_545,plain,
% 2.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | v3_tex_2(X0,sK3)
% 2.68/0.98      | k2_pre_topc(sK3,X0) != k2_struct_0(sK3) ),
% 2.68/0.98      inference(global_propositional_subsumption,
% 2.68/0.98                [status(thm)],
% 2.68/0.98                [c_541,c_33]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_546,plain,
% 2.68/0.98      ( v3_tex_2(X0,sK3)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | k2_pre_topc(sK3,X0) != k2_struct_0(sK3) ),
% 2.68/0.98      inference(renaming,[status(thm)],[c_545]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2083,plain,
% 2.68/0.98      ( k2_pre_topc(sK3,X0) != k2_struct_0(sK3)
% 2.68/0.98      | v3_tex_2(X0,sK3) = iProver_top
% 2.68/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.68/0.98      inference(predicate_to_equality,[status(thm)],[c_546]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2144,plain,
% 2.68/0.98      ( k2_pre_topc(sK3,X0) != k2_struct_0(sK3)
% 2.68/0.98      | v3_tex_2(X0,sK3) = iProver_top
% 2.68/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.68/0.98      inference(light_normalisation,[status(thm)],[c_2083,c_770]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2829,plain,
% 2.68/0.98      ( k2_struct_0(sK3) != sK4
% 2.68/0.98      | v3_tex_2(sK4,sK3) = iProver_top
% 2.68/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.68/0.98      inference(superposition,[status(thm)],[c_2335,c_2144]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_31,negated_conjecture,
% 2.68/0.98      ( v3_tex_2(sK4,sK3) | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.68/0.98      inference(cnf_transformation,[],[f97]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_274,plain,
% 2.68/0.98      ( v3_tex_2(sK4,sK3) | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.68/0.98      inference(prop_impl,[status(thm)],[c_31]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_589,plain,
% 2.68/0.98      ( v3_tex_2(sK4,sK3)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.68/0.98      | X1 = X0
% 2.68/0.98      | u1_struct_0(sK3) != X1
% 2.68/0.98      | sK4 != X0 ),
% 2.68/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_274]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_590,plain,
% 2.68/0.98      ( v3_tex_2(sK4,sK3)
% 2.68/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | u1_struct_0(sK3) = sK4 ),
% 2.68/0.98      inference(unflattening,[status(thm)],[c_589]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_592,plain,
% 2.68/0.98      ( v3_tex_2(sK4,sK3) | u1_struct_0(sK3) = sK4 ),
% 2.68/0.98      inference(global_propositional_subsumption,
% 2.68/0.98                [status(thm)],
% 2.68/0.98                [c_590,c_32]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2081,plain,
% 2.68/0.98      ( u1_struct_0(sK3) = sK4 | v3_tex_2(sK4,sK3) = iProver_top ),
% 2.68/0.98      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2103,plain,
% 2.68/0.98      ( k2_struct_0(sK3) = sK4 | v3_tex_2(sK4,sK3) = iProver_top ),
% 2.68/0.98      inference(demodulation,[status(thm)],[c_2081,c_770]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_3047,plain,
% 2.68/0.98      ( v3_tex_2(sK4,sK3) = iProver_top ),
% 2.68/0.98      inference(global_propositional_subsumption,
% 2.68/0.98                [status(thm)],
% 2.68/0.98                [c_2829,c_2103,c_2097]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_1767,plain,( X0 = X0 ),theory(equality) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2478,plain,
% 2.68/0.98      ( k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
% 2.68/0.98      inference(instantiation,[status(thm)],[c_1767]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2264,plain,
% 2.68/0.98      ( m1_subset_1(k2_subset_1(u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.68/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_23,plain,
% 2.68/0.98      ( ~ v2_tex_2(X0,X1)
% 2.68/0.98      | ~ v3_tex_2(X2,X1)
% 2.68/0.98      | ~ r1_tarski(X2,X0)
% 2.68/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.68/0.98      | ~ l1_pre_topc(X1)
% 2.68/0.98      | X0 = X2 ),
% 2.68/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_783,plain,
% 2.68/0.98      ( ~ v2_tex_2(X0,X1)
% 2.68/0.98      | ~ v3_tex_2(X2,X1)
% 2.68/0.98      | ~ r1_tarski(X2,X0)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.68/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.68/0.98      | X2 = X0
% 2.68/0.98      | sK3 != X1 ),
% 2.68/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_784,plain,
% 2.68/0.98      ( ~ v2_tex_2(X0,sK3)
% 2.68/0.98      | ~ v3_tex_2(X1,sK3)
% 2.68/0.98      | ~ r1_tarski(X1,X0)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | X1 = X0 ),
% 2.68/0.98      inference(unflattening,[status(thm)],[c_783]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_788,plain,
% 2.68/0.98      ( ~ v3_tex_2(X1,sK3)
% 2.68/0.98      | ~ r1_tarski(X1,X0)
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | X1 = X0 ),
% 2.68/0.98      inference(global_propositional_subsumption,
% 2.68/0.98                [status(thm)],
% 2.68/0.98                [c_784,c_35,c_34,c_33,c_511]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_789,plain,
% 2.68/0.98      ( ~ v3_tex_2(X0,sK3)
% 2.68/0.98      | ~ r1_tarski(X0,X1)
% 2.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | X0 = X1 ),
% 2.68/0.98      inference(renaming,[status(thm)],[c_788]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2261,plain,
% 2.68/0.98      ( ~ v3_tex_2(sK4,sK3)
% 2.68/0.98      | ~ r1_tarski(sK4,u1_struct_0(sK3))
% 2.68/0.98      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.68/0.98      | sK4 = u1_struct_0(sK3) ),
% 2.68/0.98      inference(instantiation,[status(thm)],[c_789]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2202,plain,
% 2.68/0.98      ( v3_tex_2(sK4,sK3) | k2_struct_0(sK3) = sK4 ),
% 2.68/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2103]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_30,negated_conjecture,
% 2.68/0.98      ( ~ v3_tex_2(sK4,sK3) | v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.68/0.98      inference(cnf_transformation,[],[f98]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_276,plain,
% 2.68/0.98      ( ~ v3_tex_2(sK4,sK3) | v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.68/0.98      inference(prop_impl,[status(thm)],[c_30]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_577,plain,
% 2.68/0.98      ( ~ v3_tex_2(sK4,sK3)
% 2.68/0.98      | u1_struct_0(sK3) != X0
% 2.68/0.98      | k2_subset_1(X0) != sK4 ),
% 2.68/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_276]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_578,plain,
% 2.68/0.98      ( ~ v3_tex_2(sK4,sK3) | k2_subset_1(u1_struct_0(sK3)) != sK4 ),
% 2.68/0.98      inference(unflattening,[status(thm)],[c_577]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2082,plain,
% 2.68/0.98      ( k2_subset_1(u1_struct_0(sK3)) != sK4
% 2.68/0.98      | v3_tex_2(sK4,sK3) != iProver_top ),
% 2.68/0.98      inference(predicate_to_equality,[status(thm)],[c_578]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2108,plain,
% 2.68/0.98      ( k2_subset_1(k2_struct_0(sK3)) != sK4
% 2.68/0.98      | v3_tex_2(sK4,sK3) != iProver_top ),
% 2.68/0.98      inference(light_normalisation,[status(thm)],[c_2082,c_770]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2109,plain,
% 2.68/0.98      ( k2_struct_0(sK3) != sK4 | v3_tex_2(sK4,sK3) != iProver_top ),
% 2.68/0.98      inference(demodulation,[status(thm)],[c_2108,c_0]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_579,plain,
% 2.68/0.98      ( k2_subset_1(u1_struct_0(sK3)) != sK4
% 2.68/0.98      | v3_tex_2(sK4,sK3) != iProver_top ),
% 2.68/0.98      inference(predicate_to_equality,[status(thm)],[c_578]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(contradiction,plain,
% 2.68/0.98      ( $false ),
% 2.68/0.98      inference(minisat,
% 2.68/0.98                [status(thm)],
% 2.68/0.98                [c_3975,c_3873,c_3872,c_3548,c_3544,c_3421,c_3314,c_3047,
% 2.68/0.98                 c_2478,c_2264,c_2261,c_2202,c_2109,c_579,c_32]) ).
% 2.68/0.98  
% 2.68/0.98  
% 2.68/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.68/0.98  
% 2.68/0.98  ------                               Statistics
% 2.68/0.98  
% 2.68/0.98  ------ General
% 2.68/0.98  
% 2.68/0.98  abstr_ref_over_cycles:                  0
% 2.68/0.98  abstr_ref_under_cycles:                 0
% 2.68/0.98  gc_basic_clause_elim:                   0
% 2.68/0.98  forced_gc_time:                         0
% 2.68/0.98  parsing_time:                           0.01
% 2.68/0.98  unif_index_cands_time:                  0.
% 2.68/0.98  unif_index_add_time:                    0.
% 2.68/0.98  orderings_time:                         0.
% 2.68/0.98  out_proof_time:                         0.01
% 2.68/0.98  total_time:                             0.143
% 2.68/0.98  num_of_symbols:                         56
% 2.68/0.98  num_of_terms:                           2684
% 2.68/0.98  
% 2.68/0.98  ------ Preprocessing
% 2.68/0.98  
% 2.68/0.98  num_of_splits:                          0
% 2.68/0.98  num_of_split_atoms:                     0
% 2.68/0.98  num_of_reused_defs:                     0
% 2.68/0.98  num_eq_ax_congr_red:                    38
% 2.68/0.98  num_of_sem_filtered_clauses:            1
% 2.68/0.98  num_of_subtypes:                        0
% 2.68/0.98  monotx_restored_types:                  0
% 2.68/0.98  sat_num_of_epr_types:                   0
% 2.68/0.98  sat_num_of_non_cyclic_types:            0
% 2.68/0.98  sat_guarded_non_collapsed_types:        0
% 2.68/0.98  num_pure_diseq_elim:                    0
% 2.68/0.98  simp_replaced_by:                       0
% 2.68/0.98  res_preprocessed:                       119
% 2.68/0.98  prep_upred:                             0
% 2.68/0.98  prep_unflattend:                        54
% 2.68/0.98  smt_new_axioms:                         0
% 2.68/0.98  pred_elim_cands:                        4
% 2.68/0.98  pred_elim:                              10
% 2.68/0.98  pred_elim_cl:                           18
% 2.68/0.98  pred_elim_cycles:                       14
% 2.68/0.98  merged_defs:                            2
% 2.68/0.98  merged_defs_ncl:                        0
% 2.68/0.98  bin_hyper_res:                          2
% 2.68/0.98  prep_cycles:                            4
% 2.68/0.98  pred_elim_time:                         0.022
% 2.68/0.98  splitting_time:                         0.
% 2.68/0.98  sem_filter_time:                        0.
% 2.68/0.98  monotx_time:                            0.001
% 2.68/0.98  subtype_inf_time:                       0.
% 2.68/0.98  
% 2.68/0.98  ------ Problem properties
% 2.68/0.98  
% 2.68/0.98  clauses:                                19
% 2.68/0.98  conjectures:                            1
% 2.68/0.98  epr:                                    0
% 2.68/0.98  horn:                                   14
% 2.68/0.98  ground:                                 5
% 2.68/0.98  unary:                                  5
% 2.68/0.98  binary:                                 4
% 2.68/0.98  lits:                                   48
% 2.68/0.98  lits_eq:                                10
% 2.68/0.98  fd_pure:                                0
% 2.68/0.98  fd_pseudo:                              0
% 2.68/0.98  fd_cond:                                0
% 2.68/0.98  fd_pseudo_cond:                         1
% 2.68/0.98  ac_symbols:                             0
% 2.68/0.98  
% 2.68/0.98  ------ Propositional Solver
% 2.68/0.98  
% 2.68/0.98  prop_solver_calls:                      28
% 2.68/0.98  prop_fast_solver_calls:                 1063
% 2.68/0.98  smt_solver_calls:                       0
% 2.68/0.98  smt_fast_solver_calls:                  0
% 2.68/0.98  prop_num_of_clauses:                    1151
% 2.68/0.98  prop_preprocess_simplified:             4186
% 2.68/0.98  prop_fo_subsumed:                       39
% 2.68/0.98  prop_solver_time:                       0.
% 2.68/0.98  smt_solver_time:                        0.
% 2.68/0.98  smt_fast_solver_time:                   0.
% 2.68/0.98  prop_fast_solver_time:                  0.
% 2.68/0.98  prop_unsat_core_time:                   0.
% 2.68/0.98  
% 2.68/0.98  ------ QBF
% 2.68/0.98  
% 2.68/0.98  qbf_q_res:                              0
% 2.68/0.98  qbf_num_tautologies:                    0
% 2.68/0.98  qbf_prep_cycles:                        0
% 2.68/0.98  
% 2.68/0.98  ------ BMC1
% 2.68/0.98  
% 2.68/0.98  bmc1_current_bound:                     -1
% 2.68/0.98  bmc1_last_solved_bound:                 -1
% 2.68/0.98  bmc1_unsat_core_size:                   -1
% 2.68/0.98  bmc1_unsat_core_parents_size:           -1
% 2.68/0.98  bmc1_merge_next_fun:                    0
% 2.68/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.68/0.98  
% 2.68/0.98  ------ Instantiation
% 2.68/0.98  
% 2.68/0.98  inst_num_of_clauses:                    282
% 2.68/0.98  inst_num_in_passive:                    118
% 2.68/0.98  inst_num_in_active:                     159
% 2.68/0.98  inst_num_in_unprocessed:                4
% 2.68/0.98  inst_num_of_loops:                      189
% 2.68/0.98  inst_num_of_learning_restarts:          0
% 2.68/0.98  inst_num_moves_active_passive:          26
% 2.68/0.98  inst_lit_activity:                      0
% 2.68/0.98  inst_lit_activity_moves:                0
% 2.68/0.98  inst_num_tautologies:                   0
% 2.68/0.98  inst_num_prop_implied:                  0
% 2.68/0.98  inst_num_existing_simplified:           0
% 2.68/0.98  inst_num_eq_res_simplified:             0
% 2.68/0.98  inst_num_child_elim:                    0
% 2.68/0.98  inst_num_of_dismatching_blockings:      93
% 2.68/0.98  inst_num_of_non_proper_insts:           256
% 2.68/0.98  inst_num_of_duplicates:                 0
% 2.68/0.98  inst_inst_num_from_inst_to_res:         0
% 2.68/0.98  inst_dismatching_checking_time:         0.
% 2.68/0.98  
% 2.68/0.98  ------ Resolution
% 2.68/0.98  
% 2.68/0.98  res_num_of_clauses:                     0
% 2.68/0.98  res_num_in_passive:                     0
% 2.68/0.98  res_num_in_active:                      0
% 2.68/0.98  res_num_of_loops:                       123
% 2.68/0.98  res_forward_subset_subsumed:            22
% 2.68/0.98  res_backward_subset_subsumed:           0
% 2.68/0.98  res_forward_subsumed:                   1
% 2.68/0.98  res_backward_subsumed:                  0
% 2.68/0.98  res_forward_subsumption_resolution:     2
% 2.68/0.98  res_backward_subsumption_resolution:    1
% 2.68/0.98  res_clause_to_clause_subsumption:       215
% 2.68/0.98  res_orphan_elimination:                 0
% 2.68/0.98  res_tautology_del:                      34
% 2.68/0.98  res_num_eq_res_simplified:              0
% 2.68/0.98  res_num_sel_changes:                    0
% 2.68/0.98  res_moves_from_active_to_pass:          0
% 2.68/0.98  
% 2.68/0.98  ------ Superposition
% 2.68/0.98  
% 2.68/0.98  sup_time_total:                         0.
% 2.68/0.98  sup_time_generating:                    0.
% 2.68/0.98  sup_time_sim_full:                      0.
% 2.68/0.98  sup_time_sim_immed:                     0.
% 2.68/0.98  
% 2.68/0.98  sup_num_of_clauses:                     58
% 2.68/0.98  sup_num_in_active:                      35
% 2.68/0.98  sup_num_in_passive:                     23
% 2.68/0.98  sup_num_of_loops:                       36
% 2.68/0.98  sup_fw_superposition:                   34
% 2.68/0.98  sup_bw_superposition:                   18
% 2.68/0.98  sup_immediate_simplified:               7
% 2.68/0.98  sup_given_eliminated:                   0
% 2.68/0.98  comparisons_done:                       0
% 2.68/0.98  comparisons_avoided:                    0
% 2.68/0.98  
% 2.68/0.98  ------ Simplifications
% 2.68/0.98  
% 2.68/0.98  
% 2.68/0.98  sim_fw_subset_subsumed:                 2
% 2.68/0.98  sim_bw_subset_subsumed:                 4
% 2.68/0.98  sim_fw_subsumed:                        3
% 2.68/0.98  sim_bw_subsumed:                        2
% 2.68/0.98  sim_fw_subsumption_res:                 1
% 2.68/0.98  sim_bw_subsumption_res:                 0
% 2.68/0.98  sim_tautology_del:                      1
% 2.68/0.98  sim_eq_tautology_del:                   2
% 2.68/0.98  sim_eq_res_simp:                        0
% 2.68/0.98  sim_fw_demodulated:                     2
% 2.68/0.98  sim_bw_demodulated:                     0
% 2.68/0.98  sim_light_normalised:                   10
% 2.68/0.98  sim_joinable_taut:                      0
% 2.68/0.98  sim_joinable_simp:                      0
% 2.68/0.98  sim_ac_normalised:                      0
% 2.68/0.98  sim_smt_subsumption:                    0
% 2.68/0.98  
%------------------------------------------------------------------------------
