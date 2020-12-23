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
% DateTime   : Thu Dec  3 12:27:50 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  203 (1615 expanded)
%              Number of clauses        :  144 ( 407 expanded)
%              Number of leaves         :   17 ( 437 expanded)
%              Depth                    :   25
%              Number of atoms          : 1016 (15380 expanded)
%              Number of equality atoms :  139 ( 273 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( v3_tex_2(X2,X0)
                      & r1_tarski(X1,X2) ) )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_tex_2(sK2(X0,X1),X0)
        & r1_tarski(X1,sK2(X0,X1))
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(sK2(X0,X1),X0)
            & r1_tarski(X1,sK2(X0,X1))
            & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f33])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( v4_tex_2(X2,X0)
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( v4_tex_2(X2,X0)
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ v4_tex_2(X2,X0)
            | ~ m1_pre_topc(sK4,X2)
            | ~ m1_pre_topc(X2,X0)
            | ~ v1_pre_topc(X2)
            | v2_struct_0(X2) )
        & m1_pre_topc(sK4,X0)
        & v1_tdlat_3(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ~ v4_tex_2(X2,X0)
                | ~ m1_pre_topc(X1,X2)
                | ~ m1_pre_topc(X2,X0)
                | ~ v1_pre_topc(X2)
                | v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ~ v4_tex_2(X2,sK3)
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,sK3)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & m1_pre_topc(X1,sK3)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v3_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ! [X2] :
        ( ~ v4_tex_2(X2,sK3)
        | ~ m1_pre_topc(sK4,X2)
        | ~ m1_pre_topc(X2,sK3)
        | ~ v1_pre_topc(X2)
        | v2_struct_0(X2) )
    & m1_pre_topc(sK4,sK3)
    & v1_tdlat_3(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v3_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f36,f35])).

fof(f57,plain,(
    v3_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    v1_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    ! [X2] :
      ( ~ v4_tex_2(X2,sK3)
      | ~ m1_pre_topc(sK4,X2)
      | ~ m1_pre_topc(X2,sK3)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
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

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK1(X0,X1)) = X1
        & m1_pre_topc(sK1(X0,X1),X0)
        & v1_pre_topc(sK1(X0,X1))
        & ~ v2_struct_0(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK1(X0,X1)) = X1
            & m1_pre_topc(sK1(X0,X1),X0)
            & v1_pre_topc(sK1(X0,X1))
            & ~ v2_struct_0(sK1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f30])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(sK1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v3_tex_2(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_tex_2(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_tex_2(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_tex_2(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_tex_2(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_tex_2(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK0(X0,X1),X0)
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ( ~ v3_tex_2(sK0(X0,X1),X0)
                & u1_struct_0(X1) = sK0(X0,X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v4_tex_2(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(sK0(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2108,plain,
    ( ~ v3_tex_2(X0_48,X0_49)
    | v3_tex_2(X1_48,X1_49)
    | X1_49 != X0_49
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_2755,plain,
    ( v3_tex_2(X0_48,X0_49)
    | ~ v3_tex_2(u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))),sK3)
    | X0_49 != sK3
    | X0_48 != u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) ),
    inference(instantiation,[status(thm)],[c_2108])).

cnf(c_3661,plain,
    ( v3_tex_2(sK0(sK3,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))),X0_49)
    | ~ v3_tex_2(u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))),sK3)
    | X0_49 != sK3
    | sK0(sK3,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) != u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) ),
    inference(instantiation,[status(thm)],[c_2755])).

cnf(c_3663,plain,
    ( v3_tex_2(sK0(sK3,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))),sK3)
    | ~ v3_tex_2(u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))),sK3)
    | sK3 != sK3
    | sK0(sK3,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) != u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) ),
    inference(instantiation,[status(thm)],[c_3661])).

cnf(c_2101,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_2773,plain,
    ( sK2(sK3,u1_struct_0(sK4)) != X0_48
    | sK2(sK3,u1_struct_0(sK4)) = u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4))))
    | u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) != X0_48 ),
    inference(instantiation,[status(thm)],[c_2101])).

cnf(c_3089,plain,
    ( sK2(sK3,u1_struct_0(sK4)) != sK2(sK3,u1_struct_0(sK4))
    | sK2(sK3,u1_struct_0(sK4)) = u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4))))
    | u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) != sK2(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2773])).

cnf(c_11,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_154,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_tex_2(u1_struct_0(X0),X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_0])).

cnf(c_155,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_154])).

cnf(c_16,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,negated_conjecture,
    ( v3_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_400,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_401,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_405,plain,
    ( m1_subset_1(sK2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_401,c_24,c_23,c_21])).

cnf(c_406,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_405])).

cnf(c_845,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(sK3,X2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_155,c_406])).

cnf(c_846,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | m1_subset_1(sK2(sK3,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_845])).

cnf(c_850,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | m1_subset_1(sK2(sK3,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_846,c_24,c_21])).

cnf(c_19,negated_conjecture,
    ( v1_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_929,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | m1_subset_1(sK2(sK3,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_850,c_19])).

cnf(c_930,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_929])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_932,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_930,c_20,c_18])).

cnf(c_933,plain,
    ( m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_932])).

cnf(c_2095,plain,
    ( m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_933])).

cnf(c_2359,plain,
    ( m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2095])).

cnf(c_31,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_934,plain,
    ( m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_933])).

cnf(c_1222,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_1223,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_1222])).

cnf(c_2090,plain,
    ( ~ m1_pre_topc(X0_49,sK3)
    | m1_subset_1(u1_struct_0(X0_49),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1223])).

cnf(c_2466,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_2090])).

cnf(c_2467,plain,
    ( m1_pre_topc(sK4,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2466])).

cnf(c_2498,plain,
    ( m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2359,c_31,c_934,c_2467])).

cnf(c_17,negated_conjecture,
    ( ~ v4_tex_2(X0,sK3)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK4,X0)
    | ~ v1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_pre_topc(sK1(X1,X0))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1138,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_pre_topc(sK1(X1,X0))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_1139,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_pre_topc(sK1(sK3,X0))
    | v1_xboole_0(X0)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1138])).

cnf(c_1143,plain,
    ( v1_xboole_0(X0)
    | v1_pre_topc(sK1(sK3,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1139,c_24])).

cnf(c_1144,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_pre_topc(sK1(sK3,X0))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1143])).

cnf(c_1313,plain,
    ( ~ v4_tex_2(X0,sK3)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK4,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X1)
    | v2_struct_0(X0)
    | sK1(sK3,X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1144])).

cnf(c_1314,plain,
    ( ~ v4_tex_2(sK1(sK3,X0),sK3)
    | ~ m1_pre_topc(sK1(sK3,X0),sK3)
    | ~ m1_pre_topc(sK4,sK1(sK3,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0)
    | v2_struct_0(sK1(sK3,X0)) ),
    inference(unflattening,[status(thm)],[c_1313])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1117,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_1118,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0)
    | ~ v2_struct_0(sK1(sK3,X0))
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1117])).

cnf(c_8,plain,
    ( m1_pre_topc(sK1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_xboole_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1234,plain,
    ( m1_pre_topc(sK1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_xboole_0(X1)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_1235,plain,
    ( m1_pre_topc(sK1(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1234])).

cnf(c_1318,plain,
    ( v1_xboole_0(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_pre_topc(sK4,sK1(sK3,X0))
    | ~ v4_tex_2(sK1(sK3,X0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1314,c_24,c_1118,c_1235])).

cnf(c_1319,plain,
    ( ~ v4_tex_2(sK1(sK3,X0),sK3)
    | ~ m1_pre_topc(sK4,sK1(sK3,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1318])).

cnf(c_13,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_475,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_476,plain,
    ( ~ v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_480,plain,
    ( ~ v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_24,c_21])).

cnf(c_1342,plain,
    ( ~ v3_tex_2(X0,sK3)
    | ~ v4_tex_2(sK1(sK3,X0),sK3)
    | ~ m1_pre_topc(sK4,sK1(sK3,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[status(thm)],[c_1319,c_480])).

cnf(c_2087,plain,
    ( ~ v3_tex_2(X0_48,sK3)
    | ~ v4_tex_2(sK1(sK3,X0_48),sK3)
    | ~ m1_pre_topc(sK4,sK1(sK3,X0_48))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1342])).

cnf(c_2367,plain,
    ( v3_tex_2(X0_48,sK3) != iProver_top
    | v4_tex_2(sK1(sK3,X0_48),sK3) != iProver_top
    | m1_pre_topc(sK4,sK1(sK3,X0_48)) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2087])).

cnf(c_2989,plain,
    ( v3_tex_2(sK2(sK3,u1_struct_0(sK4)),sK3) != iProver_top
    | v4_tex_2(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3) != iProver_top
    | m1_pre_topc(sK4,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2498,c_2367])).

cnf(c_14,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_442,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_443,plain,
    ( ~ v2_tex_2(X0,sK3)
    | v3_tex_2(sK2(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_tex_2(sK2(sK3,X0),sK3)
    | ~ v2_tex_2(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_443,c_24,c_23,c_21])).

cnf(c_448,plain,
    ( ~ v2_tex_2(X0,sK3)
    | v3_tex_2(sK2(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_447])).

cnf(c_818,plain,
    ( v3_tex_2(sK2(sK3,X0),sK3)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != X0
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_155,c_448])).

cnf(c_819,plain,
    ( v3_tex_2(sK2(sK3,u1_struct_0(X0)),sK3)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_818])).

cnf(c_823,plain,
    ( v3_tex_2(sK2(sK3,u1_struct_0(X0)),sK3)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_819,c_24,c_21])).

cnf(c_943,plain,
    ( v3_tex_2(sK2(sK3,u1_struct_0(X0)),sK3)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_823,c_19])).

cnf(c_944,plain,
    ( v3_tex_2(sK2(sK3,u1_struct_0(sK4)),sK3)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_943])).

cnf(c_946,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_tex_2(sK2(sK3,u1_struct_0(sK4)),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_944,c_20,c_18])).

cnf(c_947,plain,
    ( v3_tex_2(sK2(sK3,u1_struct_0(sK4)),sK3)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_946])).

cnf(c_1563,plain,
    ( ~ v4_tex_2(sK1(sK3,X0),sK3)
    | ~ m1_pre_topc(sK4,sK1(sK3,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK2(sK3,u1_struct_0(sK4)) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_1342,c_947])).

cnf(c_1564,plain,
    ( ~ v4_tex_2(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
    | ~ m1_pre_topc(sK4,sK1(sK3,sK2(sK3,u1_struct_0(sK4))))
    | ~ m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_1563])).

cnf(c_1566,plain,
    ( ~ m1_pre_topc(sK4,sK1(sK3,sK2(sK3,u1_struct_0(sK4))))
    | ~ v4_tex_2(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1564,c_20,c_18,c_930])).

cnf(c_1567,plain,
    ( ~ v4_tex_2(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
    | ~ m1_pre_topc(sK4,sK1(sK3,sK2(sK3,u1_struct_0(sK4))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_1566])).

cnf(c_1568,plain,
    ( v4_tex_2(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3) != iProver_top
    | m1_pre_topc(sK4,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1567])).

cnf(c_3071,plain,
    ( v4_tex_2(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3) != iProver_top
    | m1_pre_topc(sK4,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2989,c_31,c_1568,c_2467])).

cnf(c_3073,plain,
    ( ~ v4_tex_2(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
    | ~ m1_pre_topc(sK4,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3071])).

cnf(c_2521,plain,
    ( v3_tex_2(X0_48,X0_49)
    | ~ v3_tex_2(sK2(sK3,u1_struct_0(sK4)),sK3)
    | X0_49 != sK3
    | X0_48 != sK2(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2108])).

cnf(c_2662,plain,
    ( ~ v3_tex_2(sK2(sK3,u1_struct_0(sK4)),sK3)
    | v3_tex_2(u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))),X0_49)
    | X0_49 != sK3
    | u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) != sK2(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2521])).

cnf(c_2664,plain,
    ( ~ v3_tex_2(sK2(sK3,u1_struct_0(sK4)),sK3)
    | v3_tex_2(u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))),sK3)
    | sK3 != sK3
    | u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) != sK2(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2662])).

cnf(c_2098,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_2650,plain,
    ( sK2(sK3,u1_struct_0(sK4)) = sK2(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2098])).

cnf(c_2635,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2098])).

cnf(c_2,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_496,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_23])).

cnf(c_497,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(X1,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_499,plain,
    ( ~ m1_pre_topc(X1,sK3)
    | ~ m1_pre_topc(X0,sK3)
    | m1_pre_topc(X0,X1)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_497,c_21])).

cnf(c_500,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(X1,sK3) ),
    inference(renaming,[status(thm)],[c_499])).

cnf(c_15,plain,
    ( ~ v2_tex_2(X0,X1)
    | r1_tarski(X0,sK2(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_421,plain,
    ( ~ v2_tex_2(X0,X1)
    | r1_tarski(X0,sK2(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_422,plain,
    ( ~ v2_tex_2(X0,sK3)
    | r1_tarski(X0,sK2(sK3,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(X0,sK2(sK3,X0))
    | ~ v2_tex_2(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_422,c_24,c_23,c_21])).

cnf(c_427,plain,
    ( ~ v2_tex_2(X0,sK3)
    | r1_tarski(X0,sK2(sK3,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_426])).

cnf(c_555,plain,
    ( ~ v2_tex_2(X0,sK3)
    | m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X1,sK3)
    | ~ m1_pre_topc(X2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK2(sK3,X0) != u1_struct_0(X2)
    | u1_struct_0(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_500,c_427])).

cnf(c_556,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),sK3)
    | m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK3)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK2(sK3,u1_struct_0(X0)) != u1_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_872,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,sK3)
    | ~ m1_pre_topc(X3,sK3)
    | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | sK2(sK3,u1_struct_0(X2)) != u1_struct_0(X3)
    | u1_struct_0(X2) != u1_struct_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_155,c_556])).

cnf(c_873,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(X2,sK3)
    | ~ m1_pre_topc(X1,sK3)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(X2)
    | v2_struct_0(X2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | sK2(sK3,u1_struct_0(X0)) != u1_struct_0(X1)
    | u1_struct_0(X0) != u1_struct_0(X2) ),
    inference(unflattening,[status(thm)],[c_872])).

cnf(c_875,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(X2,sK3)
    | ~ m1_pre_topc(X1,sK3)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(X2)
    | v2_struct_0(X2)
    | sK2(sK3,u1_struct_0(X0)) != u1_struct_0(X1)
    | u1_struct_0(X0) != u1_struct_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_873,c_24,c_21])).

cnf(c_876,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,sK3)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(X1,sK3)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(X2)
    | v2_struct_0(X2)
    | sK2(sK3,u1_struct_0(X0)) != u1_struct_0(X1)
    | u1_struct_0(X0) != u1_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_875])).

cnf(c_957,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK3)
    | ~ m1_pre_topc(X2,sK3)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(X2)
    | sK2(sK3,u1_struct_0(X0)) != u1_struct_0(X1)
    | u1_struct_0(X0) != u1_struct_0(X2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_876])).

cnf(c_958,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(X1,sK3)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK4)
    | sK2(sK3,u1_struct_0(X0)) != u1_struct_0(X1)
    | u1_struct_0(X0) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_957])).

cnf(c_960,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(X1,sK3)
    | sK2(sK3,u1_struct_0(X0)) != u1_struct_0(X1)
    | u1_struct_0(X0) != u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_958,c_20,c_18])).

cnf(c_961,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(X1,sK3)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK2(sK3,u1_struct_0(X0)) != u1_struct_0(X1)
    | u1_struct_0(X0) != u1_struct_0(sK4) ),
    inference(renaming,[status(thm)],[c_960])).

cnf(c_1302,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(X1,sK3)
    | sK2(sK3,u1_struct_0(X0)) != u1_struct_0(X1)
    | u1_struct_0(X0) != u1_struct_0(sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1223,c_961])).

cnf(c_2088,plain,
    ( m1_pre_topc(X0_49,X1_49)
    | ~ m1_pre_topc(X0_49,sK3)
    | ~ m1_pre_topc(X1_49,sK3)
    | sK2(sK3,u1_struct_0(X0_49)) != u1_struct_0(X1_49)
    | u1_struct_0(X0_49) != u1_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_1302])).

cnf(c_2483,plain,
    ( ~ m1_pre_topc(X0_49,sK3)
    | m1_pre_topc(sK4,X0_49)
    | ~ m1_pre_topc(sK4,sK3)
    | sK2(sK3,u1_struct_0(sK4)) != u1_struct_0(X0_49)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2088])).

cnf(c_2617,plain,
    ( ~ m1_pre_topc(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
    | m1_pre_topc(sK4,sK1(sK3,sK2(sK3,u1_struct_0(sK4))))
    | ~ m1_pre_topc(sK4,sK3)
    | sK2(sK3,u1_struct_0(sK4)) != u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4))))
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2483])).

cnf(c_4,plain,
    ( v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1201,plain,
    ( v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | sK0(X1,X0) = u1_struct_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_1202,plain,
    ( v4_tex_2(X0,sK3)
    | ~ m1_pre_topc(X0,sK3)
    | v2_struct_0(sK3)
    | sK0(sK3,X0) = u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1201])).

cnf(c_1206,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | v4_tex_2(X0,sK3)
    | sK0(sK3,X0) = u1_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1202,c_24])).

cnf(c_1207,plain,
    ( v4_tex_2(X0,sK3)
    | ~ m1_pre_topc(X0,sK3)
    | sK0(sK3,X0) = u1_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1206])).

cnf(c_2091,plain,
    ( v4_tex_2(X0_49,sK3)
    | ~ m1_pre_topc(X0_49,sK3)
    | sK0(sK3,X0_49) = u1_struct_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_1207])).

cnf(c_2557,plain,
    ( v4_tex_2(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
    | ~ m1_pre_topc(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
    | sK0(sK3,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) = u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) ),
    inference(instantiation,[status(thm)],[c_2091])).

cnf(c_3,plain,
    ( ~ v3_tex_2(sK0(X0,X1),X0)
    | v4_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1255,plain,
    ( ~ v3_tex_2(sK0(X0,X1),X0)
    | v4_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_1256,plain,
    ( ~ v3_tex_2(sK0(sK3,X0),sK3)
    | v4_tex_2(X0,sK3)
    | ~ m1_pre_topc(X0,sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1255])).

cnf(c_1260,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | v4_tex_2(X0,sK3)
    | ~ v3_tex_2(sK0(sK3,X0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1256,c_24])).

cnf(c_1261,plain,
    ( ~ v3_tex_2(sK0(sK3,X0),sK3)
    | v4_tex_2(X0,sK3)
    | ~ m1_pre_topc(X0,sK3) ),
    inference(renaming,[status(thm)],[c_1260])).

cnf(c_2089,plain,
    ( ~ v3_tex_2(sK0(sK3,X0_49),sK3)
    | v4_tex_2(X0_49,sK3)
    | ~ m1_pre_topc(X0_49,sK3) ),
    inference(subtyping,[status(esa)],[c_1261])).

cnf(c_2559,plain,
    ( ~ v3_tex_2(sK0(sK3,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))),sK3)
    | v4_tex_2(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
    | ~ m1_pre_topc(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_2089])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1159,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | u1_struct_0(sK1(X1,X0)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_1160,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0)
    | v2_struct_0(sK3)
    | u1_struct_0(sK1(sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_1159])).

cnf(c_1164,plain,
    ( v1_xboole_0(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1160,c_24])).

cnf(c_1165,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(sK3,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_1164])).

cnf(c_1373,plain,
    ( ~ v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK1(sK3,X0)) = X0 ),
    inference(resolution,[status(thm)],[c_1165,c_480])).

cnf(c_2085,plain,
    ( ~ v3_tex_2(X0_48,sK3)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK1(sK3,X0_48)) = X0_48 ),
    inference(subtyping,[status(esa)],[c_1373])).

cnf(c_2513,plain,
    ( ~ v3_tex_2(sK2(sK3,u1_struct_0(sK4)),sK3)
    | ~ m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) = sK2(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2085])).

cnf(c_2099,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_2122,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2099])).

cnf(c_1239,plain,
    ( v1_xboole_0(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_pre_topc(sK1(sK3,X0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1235,c_24])).

cnf(c_1240,plain,
    ( m1_pre_topc(sK1(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1239])).

cnf(c_1359,plain,
    ( ~ v3_tex_2(X0,sK3)
    | m1_pre_topc(sK1(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[status(thm)],[c_1240,c_480])).

cnf(c_1549,plain,
    ( m1_pre_topc(sK1(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK2(sK3,u1_struct_0(sK4)) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_1359,c_947])).

cnf(c_1550,plain,
    ( m1_pre_topc(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
    | ~ m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_1549])).

cnf(c_1552,plain,
    ( m1_pre_topc(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1550,c_20,c_18,c_930])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3663,c_3089,c_3073,c_2664,c_2650,c_2635,c_2617,c_2557,c_2559,c_2513,c_2466,c_2122,c_1552,c_947,c_933,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:57:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.16/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/0.99  
% 2.16/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.16/0.99  
% 2.16/0.99  ------  iProver source info
% 2.16/0.99  
% 2.16/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.16/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.16/0.99  git: non_committed_changes: false
% 2.16/0.99  git: last_make_outside_of_git: false
% 2.16/0.99  
% 2.16/0.99  ------ 
% 2.16/0.99  
% 2.16/0.99  ------ Input Options
% 2.16/0.99  
% 2.16/0.99  --out_options                           all
% 2.16/0.99  --tptp_safe_out                         true
% 2.16/0.99  --problem_path                          ""
% 2.16/0.99  --include_path                          ""
% 2.16/0.99  --clausifier                            res/vclausify_rel
% 2.16/0.99  --clausifier_options                    --mode clausify
% 2.16/0.99  --stdin                                 false
% 2.16/0.99  --stats_out                             all
% 2.16/0.99  
% 2.16/0.99  ------ General Options
% 2.16/0.99  
% 2.16/0.99  --fof                                   false
% 2.16/0.99  --time_out_real                         305.
% 2.16/0.99  --time_out_virtual                      -1.
% 2.16/0.99  --symbol_type_check                     false
% 2.16/0.99  --clausify_out                          false
% 2.16/0.99  --sig_cnt_out                           false
% 2.16/0.99  --trig_cnt_out                          false
% 2.16/0.99  --trig_cnt_out_tolerance                1.
% 2.16/0.99  --trig_cnt_out_sk_spl                   false
% 2.16/0.99  --abstr_cl_out                          false
% 2.16/0.99  
% 2.16/0.99  ------ Global Options
% 2.16/0.99  
% 2.16/0.99  --schedule                              default
% 2.16/0.99  --add_important_lit                     false
% 2.16/0.99  --prop_solver_per_cl                    1000
% 2.16/0.99  --min_unsat_core                        false
% 2.16/0.99  --soft_assumptions                      false
% 2.16/0.99  --soft_lemma_size                       3
% 2.16/0.99  --prop_impl_unit_size                   0
% 2.16/0.99  --prop_impl_unit                        []
% 2.16/0.99  --share_sel_clauses                     true
% 2.16/0.99  --reset_solvers                         false
% 2.16/0.99  --bc_imp_inh                            [conj_cone]
% 2.16/0.99  --conj_cone_tolerance                   3.
% 2.16/0.99  --extra_neg_conj                        none
% 2.16/0.99  --large_theory_mode                     true
% 2.16/0.99  --prolific_symb_bound                   200
% 2.16/0.99  --lt_threshold                          2000
% 2.16/0.99  --clause_weak_htbl                      true
% 2.16/0.99  --gc_record_bc_elim                     false
% 2.16/0.99  
% 2.16/0.99  ------ Preprocessing Options
% 2.16/0.99  
% 2.16/0.99  --preprocessing_flag                    true
% 2.16/0.99  --time_out_prep_mult                    0.1
% 2.16/0.99  --splitting_mode                        input
% 2.16/0.99  --splitting_grd                         true
% 2.16/0.99  --splitting_cvd                         false
% 2.16/0.99  --splitting_cvd_svl                     false
% 2.16/0.99  --splitting_nvd                         32
% 2.16/0.99  --sub_typing                            true
% 2.16/0.99  --prep_gs_sim                           true
% 2.16/0.99  --prep_unflatten                        true
% 2.16/0.99  --prep_res_sim                          true
% 2.16/0.99  --prep_upred                            true
% 2.16/0.99  --prep_sem_filter                       exhaustive
% 2.16/0.99  --prep_sem_filter_out                   false
% 2.16/0.99  --pred_elim                             true
% 2.16/0.99  --res_sim_input                         true
% 2.16/0.99  --eq_ax_congr_red                       true
% 2.16/0.99  --pure_diseq_elim                       true
% 2.16/0.99  --brand_transform                       false
% 2.16/0.99  --non_eq_to_eq                          false
% 2.16/0.99  --prep_def_merge                        true
% 2.16/0.99  --prep_def_merge_prop_impl              false
% 2.16/0.99  --prep_def_merge_mbd                    true
% 2.16/0.99  --prep_def_merge_tr_red                 false
% 2.16/0.99  --prep_def_merge_tr_cl                  false
% 2.16/0.99  --smt_preprocessing                     true
% 2.16/0.99  --smt_ac_axioms                         fast
% 2.16/0.99  --preprocessed_out                      false
% 2.16/0.99  --preprocessed_stats                    false
% 2.16/0.99  
% 2.16/0.99  ------ Abstraction refinement Options
% 2.16/0.99  
% 2.16/0.99  --abstr_ref                             []
% 2.16/0.99  --abstr_ref_prep                        false
% 2.16/0.99  --abstr_ref_until_sat                   false
% 2.16/0.99  --abstr_ref_sig_restrict                funpre
% 2.16/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/0.99  --abstr_ref_under                       []
% 2.16/0.99  
% 2.16/0.99  ------ SAT Options
% 2.16/0.99  
% 2.16/0.99  --sat_mode                              false
% 2.16/0.99  --sat_fm_restart_options                ""
% 2.16/0.99  --sat_gr_def                            false
% 2.16/0.99  --sat_epr_types                         true
% 2.16/0.99  --sat_non_cyclic_types                  false
% 2.16/0.99  --sat_finite_models                     false
% 2.16/0.99  --sat_fm_lemmas                         false
% 2.16/0.99  --sat_fm_prep                           false
% 2.16/0.99  --sat_fm_uc_incr                        true
% 2.16/0.99  --sat_out_model                         small
% 2.16/0.99  --sat_out_clauses                       false
% 2.16/0.99  
% 2.16/0.99  ------ QBF Options
% 2.16/0.99  
% 2.16/0.99  --qbf_mode                              false
% 2.16/0.99  --qbf_elim_univ                         false
% 2.16/0.99  --qbf_dom_inst                          none
% 2.16/0.99  --qbf_dom_pre_inst                      false
% 2.16/0.99  --qbf_sk_in                             false
% 2.16/0.99  --qbf_pred_elim                         true
% 2.16/0.99  --qbf_split                             512
% 2.16/0.99  
% 2.16/0.99  ------ BMC1 Options
% 2.16/0.99  
% 2.16/0.99  --bmc1_incremental                      false
% 2.16/0.99  --bmc1_axioms                           reachable_all
% 2.16/0.99  --bmc1_min_bound                        0
% 2.16/0.99  --bmc1_max_bound                        -1
% 2.16/0.99  --bmc1_max_bound_default                -1
% 2.16/0.99  --bmc1_symbol_reachability              true
% 2.16/0.99  --bmc1_property_lemmas                  false
% 2.16/0.99  --bmc1_k_induction                      false
% 2.16/0.99  --bmc1_non_equiv_states                 false
% 2.16/0.99  --bmc1_deadlock                         false
% 2.16/0.99  --bmc1_ucm                              false
% 2.16/0.99  --bmc1_add_unsat_core                   none
% 2.16/0.99  --bmc1_unsat_core_children              false
% 2.16/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/0.99  --bmc1_out_stat                         full
% 2.16/0.99  --bmc1_ground_init                      false
% 2.16/0.99  --bmc1_pre_inst_next_state              false
% 2.16/0.99  --bmc1_pre_inst_state                   false
% 2.16/0.99  --bmc1_pre_inst_reach_state             false
% 2.16/0.99  --bmc1_out_unsat_core                   false
% 2.16/0.99  --bmc1_aig_witness_out                  false
% 2.16/0.99  --bmc1_verbose                          false
% 2.16/0.99  --bmc1_dump_clauses_tptp                false
% 2.16/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.16/0.99  --bmc1_dump_file                        -
% 2.16/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.16/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.16/0.99  --bmc1_ucm_extend_mode                  1
% 2.16/0.99  --bmc1_ucm_init_mode                    2
% 2.16/0.99  --bmc1_ucm_cone_mode                    none
% 2.16/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.16/0.99  --bmc1_ucm_relax_model                  4
% 2.16/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.16/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/0.99  --bmc1_ucm_layered_model                none
% 2.16/0.99  --bmc1_ucm_max_lemma_size               10
% 2.16/0.99  
% 2.16/0.99  ------ AIG Options
% 2.16/0.99  
% 2.16/0.99  --aig_mode                              false
% 2.16/0.99  
% 2.16/0.99  ------ Instantiation Options
% 2.16/0.99  
% 2.16/0.99  --instantiation_flag                    true
% 2.16/0.99  --inst_sos_flag                         false
% 2.16/0.99  --inst_sos_phase                        true
% 2.16/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/0.99  --inst_lit_sel_side                     num_symb
% 2.16/0.99  --inst_solver_per_active                1400
% 2.16/0.99  --inst_solver_calls_frac                1.
% 2.16/0.99  --inst_passive_queue_type               priority_queues
% 2.16/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/0.99  --inst_passive_queues_freq              [25;2]
% 2.16/0.99  --inst_dismatching                      true
% 2.16/0.99  --inst_eager_unprocessed_to_passive     true
% 2.16/0.99  --inst_prop_sim_given                   true
% 2.16/0.99  --inst_prop_sim_new                     false
% 2.16/0.99  --inst_subs_new                         false
% 2.16/1.00  --inst_eq_res_simp                      false
% 2.16/1.00  --inst_subs_given                       false
% 2.16/1.00  --inst_orphan_elimination               true
% 2.16/1.00  --inst_learning_loop_flag               true
% 2.16/1.00  --inst_learning_start                   3000
% 2.16/1.00  --inst_learning_factor                  2
% 2.16/1.00  --inst_start_prop_sim_after_learn       3
% 2.16/1.00  --inst_sel_renew                        solver
% 2.16/1.00  --inst_lit_activity_flag                true
% 2.16/1.00  --inst_restr_to_given                   false
% 2.16/1.00  --inst_activity_threshold               500
% 2.16/1.00  --inst_out_proof                        true
% 2.16/1.00  
% 2.16/1.00  ------ Resolution Options
% 2.16/1.00  
% 2.16/1.00  --resolution_flag                       true
% 2.16/1.00  --res_lit_sel                           adaptive
% 2.16/1.00  --res_lit_sel_side                      none
% 2.16/1.00  --res_ordering                          kbo
% 2.16/1.00  --res_to_prop_solver                    active
% 2.16/1.00  --res_prop_simpl_new                    false
% 2.16/1.00  --res_prop_simpl_given                  true
% 2.16/1.00  --res_passive_queue_type                priority_queues
% 2.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.00  --res_passive_queues_freq               [15;5]
% 2.16/1.00  --res_forward_subs                      full
% 2.16/1.00  --res_backward_subs                     full
% 2.16/1.00  --res_forward_subs_resolution           true
% 2.16/1.00  --res_backward_subs_resolution          true
% 2.16/1.00  --res_orphan_elimination                true
% 2.16/1.00  --res_time_limit                        2.
% 2.16/1.00  --res_out_proof                         true
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Options
% 2.16/1.00  
% 2.16/1.00  --superposition_flag                    true
% 2.16/1.00  --sup_passive_queue_type                priority_queues
% 2.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.00  --demod_completeness_check              fast
% 2.16/1.00  --demod_use_ground                      true
% 2.16/1.00  --sup_to_prop_solver                    passive
% 2.16/1.00  --sup_prop_simpl_new                    true
% 2.16/1.00  --sup_prop_simpl_given                  true
% 2.16/1.00  --sup_fun_splitting                     false
% 2.16/1.00  --sup_smt_interval                      50000
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Simplification Setup
% 2.16/1.00  
% 2.16/1.00  --sup_indices_passive                   []
% 2.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_full_bw                           [BwDemod]
% 2.16/1.00  --sup_immed_triv                        [TrivRules]
% 2.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_immed_bw_main                     []
% 2.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  
% 2.16/1.00  ------ Combination Options
% 2.16/1.00  
% 2.16/1.00  --comb_res_mult                         3
% 2.16/1.00  --comb_sup_mult                         2
% 2.16/1.00  --comb_inst_mult                        10
% 2.16/1.00  
% 2.16/1.00  ------ Debug Options
% 2.16/1.00  
% 2.16/1.00  --dbg_backtrace                         false
% 2.16/1.00  --dbg_dump_prop_clauses                 false
% 2.16/1.00  --dbg_dump_prop_clauses_file            -
% 2.16/1.00  --dbg_out_stat                          false
% 2.16/1.00  ------ Parsing...
% 2.16/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.16/1.00  ------ Proving...
% 2.16/1.00  ------ Problem Properties 
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  clauses                                 12
% 2.16/1.00  conjectures                             1
% 2.16/1.00  EPR                                     1
% 2.16/1.00  Horn                                    10
% 2.16/1.00  unary                                   1
% 2.16/1.00  binary                                  3
% 2.16/1.00  lits                                    34
% 2.16/1.00  lits eq                                 4
% 2.16/1.00  fd_pure                                 0
% 2.16/1.00  fd_pseudo                               0
% 2.16/1.00  fd_cond                                 0
% 2.16/1.00  fd_pseudo_cond                          0
% 2.16/1.00  AC symbols                              0
% 2.16/1.00  
% 2.16/1.00  ------ Schedule dynamic 5 is on 
% 2.16/1.00  
% 2.16/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  ------ 
% 2.16/1.00  Current options:
% 2.16/1.00  ------ 
% 2.16/1.00  
% 2.16/1.00  ------ Input Options
% 2.16/1.00  
% 2.16/1.00  --out_options                           all
% 2.16/1.00  --tptp_safe_out                         true
% 2.16/1.00  --problem_path                          ""
% 2.16/1.00  --include_path                          ""
% 2.16/1.00  --clausifier                            res/vclausify_rel
% 2.16/1.00  --clausifier_options                    --mode clausify
% 2.16/1.00  --stdin                                 false
% 2.16/1.00  --stats_out                             all
% 2.16/1.00  
% 2.16/1.00  ------ General Options
% 2.16/1.00  
% 2.16/1.00  --fof                                   false
% 2.16/1.00  --time_out_real                         305.
% 2.16/1.00  --time_out_virtual                      -1.
% 2.16/1.00  --symbol_type_check                     false
% 2.16/1.00  --clausify_out                          false
% 2.16/1.00  --sig_cnt_out                           false
% 2.16/1.00  --trig_cnt_out                          false
% 2.16/1.00  --trig_cnt_out_tolerance                1.
% 2.16/1.00  --trig_cnt_out_sk_spl                   false
% 2.16/1.00  --abstr_cl_out                          false
% 2.16/1.00  
% 2.16/1.00  ------ Global Options
% 2.16/1.00  
% 2.16/1.00  --schedule                              default
% 2.16/1.00  --add_important_lit                     false
% 2.16/1.00  --prop_solver_per_cl                    1000
% 2.16/1.00  --min_unsat_core                        false
% 2.16/1.00  --soft_assumptions                      false
% 2.16/1.00  --soft_lemma_size                       3
% 2.16/1.00  --prop_impl_unit_size                   0
% 2.16/1.00  --prop_impl_unit                        []
% 2.16/1.00  --share_sel_clauses                     true
% 2.16/1.00  --reset_solvers                         false
% 2.16/1.00  --bc_imp_inh                            [conj_cone]
% 2.16/1.00  --conj_cone_tolerance                   3.
% 2.16/1.00  --extra_neg_conj                        none
% 2.16/1.00  --large_theory_mode                     true
% 2.16/1.00  --prolific_symb_bound                   200
% 2.16/1.00  --lt_threshold                          2000
% 2.16/1.00  --clause_weak_htbl                      true
% 2.16/1.00  --gc_record_bc_elim                     false
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing Options
% 2.16/1.00  
% 2.16/1.00  --preprocessing_flag                    true
% 2.16/1.00  --time_out_prep_mult                    0.1
% 2.16/1.00  --splitting_mode                        input
% 2.16/1.00  --splitting_grd                         true
% 2.16/1.00  --splitting_cvd                         false
% 2.16/1.00  --splitting_cvd_svl                     false
% 2.16/1.00  --splitting_nvd                         32
% 2.16/1.00  --sub_typing                            true
% 2.16/1.00  --prep_gs_sim                           true
% 2.16/1.00  --prep_unflatten                        true
% 2.16/1.00  --prep_res_sim                          true
% 2.16/1.00  --prep_upred                            true
% 2.16/1.00  --prep_sem_filter                       exhaustive
% 2.16/1.00  --prep_sem_filter_out                   false
% 2.16/1.00  --pred_elim                             true
% 2.16/1.00  --res_sim_input                         true
% 2.16/1.00  --eq_ax_congr_red                       true
% 2.16/1.00  --pure_diseq_elim                       true
% 2.16/1.00  --brand_transform                       false
% 2.16/1.00  --non_eq_to_eq                          false
% 2.16/1.00  --prep_def_merge                        true
% 2.16/1.00  --prep_def_merge_prop_impl              false
% 2.16/1.00  --prep_def_merge_mbd                    true
% 2.16/1.00  --prep_def_merge_tr_red                 false
% 2.16/1.00  --prep_def_merge_tr_cl                  false
% 2.16/1.00  --smt_preprocessing                     true
% 2.16/1.00  --smt_ac_axioms                         fast
% 2.16/1.00  --preprocessed_out                      false
% 2.16/1.00  --preprocessed_stats                    false
% 2.16/1.00  
% 2.16/1.00  ------ Abstraction refinement Options
% 2.16/1.00  
% 2.16/1.00  --abstr_ref                             []
% 2.16/1.00  --abstr_ref_prep                        false
% 2.16/1.00  --abstr_ref_until_sat                   false
% 2.16/1.00  --abstr_ref_sig_restrict                funpre
% 2.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.00  --abstr_ref_under                       []
% 2.16/1.00  
% 2.16/1.00  ------ SAT Options
% 2.16/1.00  
% 2.16/1.00  --sat_mode                              false
% 2.16/1.00  --sat_fm_restart_options                ""
% 2.16/1.00  --sat_gr_def                            false
% 2.16/1.00  --sat_epr_types                         true
% 2.16/1.00  --sat_non_cyclic_types                  false
% 2.16/1.00  --sat_finite_models                     false
% 2.16/1.00  --sat_fm_lemmas                         false
% 2.16/1.00  --sat_fm_prep                           false
% 2.16/1.00  --sat_fm_uc_incr                        true
% 2.16/1.00  --sat_out_model                         small
% 2.16/1.00  --sat_out_clauses                       false
% 2.16/1.00  
% 2.16/1.00  ------ QBF Options
% 2.16/1.00  
% 2.16/1.00  --qbf_mode                              false
% 2.16/1.00  --qbf_elim_univ                         false
% 2.16/1.00  --qbf_dom_inst                          none
% 2.16/1.00  --qbf_dom_pre_inst                      false
% 2.16/1.00  --qbf_sk_in                             false
% 2.16/1.00  --qbf_pred_elim                         true
% 2.16/1.00  --qbf_split                             512
% 2.16/1.00  
% 2.16/1.00  ------ BMC1 Options
% 2.16/1.00  
% 2.16/1.00  --bmc1_incremental                      false
% 2.16/1.00  --bmc1_axioms                           reachable_all
% 2.16/1.00  --bmc1_min_bound                        0
% 2.16/1.00  --bmc1_max_bound                        -1
% 2.16/1.00  --bmc1_max_bound_default                -1
% 2.16/1.00  --bmc1_symbol_reachability              true
% 2.16/1.00  --bmc1_property_lemmas                  false
% 2.16/1.00  --bmc1_k_induction                      false
% 2.16/1.00  --bmc1_non_equiv_states                 false
% 2.16/1.00  --bmc1_deadlock                         false
% 2.16/1.00  --bmc1_ucm                              false
% 2.16/1.00  --bmc1_add_unsat_core                   none
% 2.16/1.00  --bmc1_unsat_core_children              false
% 2.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.00  --bmc1_out_stat                         full
% 2.16/1.00  --bmc1_ground_init                      false
% 2.16/1.00  --bmc1_pre_inst_next_state              false
% 2.16/1.00  --bmc1_pre_inst_state                   false
% 2.16/1.00  --bmc1_pre_inst_reach_state             false
% 2.16/1.00  --bmc1_out_unsat_core                   false
% 2.16/1.00  --bmc1_aig_witness_out                  false
% 2.16/1.00  --bmc1_verbose                          false
% 2.16/1.00  --bmc1_dump_clauses_tptp                false
% 2.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.00  --bmc1_dump_file                        -
% 2.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.00  --bmc1_ucm_extend_mode                  1
% 2.16/1.00  --bmc1_ucm_init_mode                    2
% 2.16/1.00  --bmc1_ucm_cone_mode                    none
% 2.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.00  --bmc1_ucm_relax_model                  4
% 2.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.00  --bmc1_ucm_layered_model                none
% 2.16/1.00  --bmc1_ucm_max_lemma_size               10
% 2.16/1.00  
% 2.16/1.00  ------ AIG Options
% 2.16/1.00  
% 2.16/1.00  --aig_mode                              false
% 2.16/1.00  
% 2.16/1.00  ------ Instantiation Options
% 2.16/1.00  
% 2.16/1.00  --instantiation_flag                    true
% 2.16/1.00  --inst_sos_flag                         false
% 2.16/1.00  --inst_sos_phase                        true
% 2.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel_side                     none
% 2.16/1.00  --inst_solver_per_active                1400
% 2.16/1.00  --inst_solver_calls_frac                1.
% 2.16/1.00  --inst_passive_queue_type               priority_queues
% 2.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.00  --inst_passive_queues_freq              [25;2]
% 2.16/1.00  --inst_dismatching                      true
% 2.16/1.00  --inst_eager_unprocessed_to_passive     true
% 2.16/1.00  --inst_prop_sim_given                   true
% 2.16/1.00  --inst_prop_sim_new                     false
% 2.16/1.00  --inst_subs_new                         false
% 2.16/1.00  --inst_eq_res_simp                      false
% 2.16/1.00  --inst_subs_given                       false
% 2.16/1.00  --inst_orphan_elimination               true
% 2.16/1.00  --inst_learning_loop_flag               true
% 2.16/1.00  --inst_learning_start                   3000
% 2.16/1.00  --inst_learning_factor                  2
% 2.16/1.00  --inst_start_prop_sim_after_learn       3
% 2.16/1.00  --inst_sel_renew                        solver
% 2.16/1.00  --inst_lit_activity_flag                true
% 2.16/1.00  --inst_restr_to_given                   false
% 2.16/1.00  --inst_activity_threshold               500
% 2.16/1.00  --inst_out_proof                        true
% 2.16/1.00  
% 2.16/1.00  ------ Resolution Options
% 2.16/1.00  
% 2.16/1.00  --resolution_flag                       false
% 2.16/1.00  --res_lit_sel                           adaptive
% 2.16/1.00  --res_lit_sel_side                      none
% 2.16/1.00  --res_ordering                          kbo
% 2.16/1.00  --res_to_prop_solver                    active
% 2.16/1.00  --res_prop_simpl_new                    false
% 2.16/1.00  --res_prop_simpl_given                  true
% 2.16/1.00  --res_passive_queue_type                priority_queues
% 2.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.00  --res_passive_queues_freq               [15;5]
% 2.16/1.00  --res_forward_subs                      full
% 2.16/1.00  --res_backward_subs                     full
% 2.16/1.00  --res_forward_subs_resolution           true
% 2.16/1.00  --res_backward_subs_resolution          true
% 2.16/1.00  --res_orphan_elimination                true
% 2.16/1.00  --res_time_limit                        2.
% 2.16/1.00  --res_out_proof                         true
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Options
% 2.16/1.00  
% 2.16/1.00  --superposition_flag                    true
% 2.16/1.00  --sup_passive_queue_type                priority_queues
% 2.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.00  --demod_completeness_check              fast
% 2.16/1.00  --demod_use_ground                      true
% 2.16/1.00  --sup_to_prop_solver                    passive
% 2.16/1.00  --sup_prop_simpl_new                    true
% 2.16/1.00  --sup_prop_simpl_given                  true
% 2.16/1.00  --sup_fun_splitting                     false
% 2.16/1.00  --sup_smt_interval                      50000
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Simplification Setup
% 2.16/1.00  
% 2.16/1.00  --sup_indices_passive                   []
% 2.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_full_bw                           [BwDemod]
% 2.16/1.00  --sup_immed_triv                        [TrivRules]
% 2.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_immed_bw_main                     []
% 2.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  
% 2.16/1.00  ------ Combination Options
% 2.16/1.00  
% 2.16/1.00  --comb_res_mult                         3
% 2.16/1.00  --comb_sup_mult                         2
% 2.16/1.00  --comb_inst_mult                        10
% 2.16/1.00  
% 2.16/1.00  ------ Debug Options
% 2.16/1.00  
% 2.16/1.00  --dbg_backtrace                         false
% 2.16/1.00  --dbg_dump_prop_clauses                 false
% 2.16/1.00  --dbg_dump_prop_clauses_file            -
% 2.16/1.00  --dbg_out_stat                          false
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  ------ Proving...
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  % SZS status Theorem for theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  fof(f5,axiom,(
% 2.16/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 2.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f17,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.16/1.00    inference(ennf_transformation,[],[f5])).
% 2.16/1.00  
% 2.16/1.00  fof(f18,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/1.00    inference(flattening,[],[f17])).
% 2.16/1.00  
% 2.16/1.00  fof(f32,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/1.00    inference(nnf_transformation,[],[f18])).
% 2.16/1.00  
% 2.16/1.00  fof(f50,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f32])).
% 2.16/1.00  
% 2.16/1.00  fof(f64,plain,(
% 2.16/1.00    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.16/1.00    inference(equality_resolution,[],[f50])).
% 2.16/1.00  
% 2.16/1.00  fof(f1,axiom,(
% 2.16/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f10,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.16/1.00    inference(ennf_transformation,[],[f1])).
% 2.16/1.00  
% 2.16/1.00  fof(f38,plain,(
% 2.16/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f10])).
% 2.16/1.00  
% 2.16/1.00  fof(f7,axiom,(
% 2.16/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 2.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f21,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : ((? [X2] : ((v3_tex_2(X2,X0) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.16/1.00    inference(ennf_transformation,[],[f7])).
% 2.16/1.00  
% 2.16/1.00  fof(f22,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/1.00    inference(flattening,[],[f21])).
% 2.16/1.00  
% 2.16/1.00  fof(f33,plain,(
% 2.16/1.00    ! [X1,X0] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_tex_2(sK2(X0,X1),X0) & r1_tarski(X1,sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f34,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : ((v3_tex_2(sK2(X0,X1),X0) & r1_tarski(X1,sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f33])).
% 2.16/1.00  
% 2.16/1.00  fof(f52,plain,(
% 2.16/1.00    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f34])).
% 2.16/1.00  
% 2.16/1.00  fof(f8,conjecture,(
% 2.16/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) => ? [X2] : (v4_tex_2(X2,X0) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 2.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f9,negated_conjecture,(
% 2.16/1.00    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) => ? [X2] : (v4_tex_2(X2,X0) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 2.16/1.00    inference(negated_conjecture,[],[f8])).
% 2.16/1.00  
% 2.16/1.00  fof(f23,plain,(
% 2.16/1.00    ? [X0] : (? [X1] : (! [X2] : (~v4_tex_2(X2,X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & (m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.16/1.00    inference(ennf_transformation,[],[f9])).
% 2.16/1.00  
% 2.16/1.00  fof(f24,plain,(
% 2.16/1.00    ? [X0] : (? [X1] : (! [X2] : (~v4_tex_2(X2,X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.16/1.00    inference(flattening,[],[f23])).
% 2.16/1.00  
% 2.16/1.00  fof(f36,plain,(
% 2.16/1.00    ( ! [X0] : (? [X1] : (! [X2] : (~v4_tex_2(X2,X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v4_tex_2(X2,X0) | ~m1_pre_topc(sK4,X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(sK4,X0) & v1_tdlat_3(sK4) & ~v2_struct_0(sK4))) )),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f35,plain,(
% 2.16/1.00    ? [X0] : (? [X1] : (! [X2] : (~v4_tex_2(X2,X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (! [X2] : (~v4_tex_2(X2,sK3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,sK3) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(X1,sK3) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f37,plain,(
% 2.16/1.00    (! [X2] : (~v4_tex_2(X2,sK3) | ~m1_pre_topc(sK4,X2) | ~m1_pre_topc(X2,sK3) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(sK4,sK3) & v1_tdlat_3(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f36,f35])).
% 2.16/1.00  
% 2.16/1.00  fof(f57,plain,(
% 2.16/1.00    v3_tdlat_3(sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f37])).
% 2.16/1.00  
% 2.16/1.00  fof(f55,plain,(
% 2.16/1.00    ~v2_struct_0(sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f37])).
% 2.16/1.00  
% 2.16/1.00  fof(f56,plain,(
% 2.16/1.00    v2_pre_topc(sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f37])).
% 2.16/1.00  
% 2.16/1.00  fof(f58,plain,(
% 2.16/1.00    l1_pre_topc(sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f37])).
% 2.16/1.00  
% 2.16/1.00  fof(f60,plain,(
% 2.16/1.00    v1_tdlat_3(sK4)),
% 2.16/1.00    inference(cnf_transformation,[],[f37])).
% 2.16/1.00  
% 2.16/1.00  fof(f59,plain,(
% 2.16/1.00    ~v2_struct_0(sK4)),
% 2.16/1.00    inference(cnf_transformation,[],[f37])).
% 2.16/1.00  
% 2.16/1.00  fof(f61,plain,(
% 2.16/1.00    m1_pre_topc(sK4,sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f37])).
% 2.16/1.00  
% 2.16/1.00  fof(f62,plain,(
% 2.16/1.00    ( ! [X2] : (~v4_tex_2(X2,sK3) | ~m1_pre_topc(sK4,X2) | ~m1_pre_topc(X2,sK3) | ~v1_pre_topc(X2) | v2_struct_0(X2)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f37])).
% 2.16/1.00  
% 2.16/1.00  fof(f4,axiom,(
% 2.16/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 2.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f15,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.16/1.00    inference(ennf_transformation,[],[f4])).
% 2.16/1.00  
% 2.16/1.00  fof(f16,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/1.00    inference(flattening,[],[f15])).
% 2.16/1.00  
% 2.16/1.00  fof(f30,plain,(
% 2.16/1.00    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & v1_pre_topc(sK1(X0,X1)) & ~v2_struct_0(sK1(X0,X1))))),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f31,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : ((u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & v1_pre_topc(sK1(X0,X1)) & ~v2_struct_0(sK1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f30])).
% 2.16/1.00  
% 2.16/1.00  fof(f46,plain,(
% 2.16/1.00    ( ! [X0,X1] : (v1_pre_topc(sK1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f31])).
% 2.16/1.00  
% 2.16/1.00  fof(f45,plain,(
% 2.16/1.00    ( ! [X0,X1] : (~v2_struct_0(sK1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f31])).
% 2.16/1.00  
% 2.16/1.00  fof(f47,plain,(
% 2.16/1.00    ( ! [X0,X1] : (m1_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f31])).
% 2.16/1.00  
% 2.16/1.00  fof(f6,axiom,(
% 2.16/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f19,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.16/1.00    inference(ennf_transformation,[],[f6])).
% 2.16/1.00  
% 2.16/1.00  fof(f20,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/1.00    inference(flattening,[],[f19])).
% 2.16/1.00  
% 2.16/1.00  fof(f51,plain,(
% 2.16/1.00    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f20])).
% 2.16/1.00  
% 2.16/1.00  fof(f54,plain,(
% 2.16/1.00    ( ! [X0,X1] : (v3_tex_2(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f34])).
% 2.16/1.00  
% 2.16/1.00  fof(f2,axiom,(
% 2.16/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 2.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f11,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.16/1.00    inference(ennf_transformation,[],[f2])).
% 2.16/1.00  
% 2.16/1.00  fof(f12,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.16/1.00    inference(flattening,[],[f11])).
% 2.16/1.00  
% 2.16/1.00  fof(f25,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.16/1.00    inference(nnf_transformation,[],[f12])).
% 2.16/1.00  
% 2.16/1.00  fof(f39,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f25])).
% 2.16/1.00  
% 2.16/1.00  fof(f53,plain,(
% 2.16/1.00    ( ! [X0,X1] : (r1_tarski(X1,sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f34])).
% 2.16/1.00  
% 2.16/1.00  fof(f3,axiom,(
% 2.16/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 2.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f13,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.16/1.00    inference(ennf_transformation,[],[f3])).
% 2.16/1.00  
% 2.16/1.00  fof(f14,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/1.00    inference(flattening,[],[f13])).
% 2.16/1.00  
% 2.16/1.00  fof(f26,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/1.00    inference(nnf_transformation,[],[f14])).
% 2.16/1.00  
% 2.16/1.00  fof(f27,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/1.00    inference(rectify,[],[f26])).
% 2.16/1.00  
% 2.16/1.00  fof(f28,plain,(
% 2.16/1.00    ! [X1,X0] : (? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK0(X0,X1),X0) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f29,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | (~v3_tex_2(sK0(X0,X1),X0) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.16/1.00  
% 2.16/1.00  fof(f43,plain,(
% 2.16/1.00    ( ! [X0,X1] : (v4_tex_2(X1,X0) | u1_struct_0(X1) = sK0(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f29])).
% 2.16/1.00  
% 2.16/1.00  fof(f44,plain,(
% 2.16/1.00    ( ! [X0,X1] : (v4_tex_2(X1,X0) | ~v3_tex_2(sK0(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f29])).
% 2.16/1.00  
% 2.16/1.00  fof(f48,plain,(
% 2.16/1.00    ( ! [X0,X1] : (u1_struct_0(sK1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f31])).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2108,plain,
% 2.16/1.00      ( ~ v3_tex_2(X0_48,X0_49)
% 2.16/1.00      | v3_tex_2(X1_48,X1_49)
% 2.16/1.00      | X1_49 != X0_49
% 2.16/1.00      | X1_48 != X0_48 ),
% 2.16/1.00      theory(equality) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2755,plain,
% 2.16/1.00      ( v3_tex_2(X0_48,X0_49)
% 2.16/1.00      | ~ v3_tex_2(u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))),sK3)
% 2.16/1.00      | X0_49 != sK3
% 2.16/1.00      | X0_48 != u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2108]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_3661,plain,
% 2.16/1.00      ( v3_tex_2(sK0(sK3,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))),X0_49)
% 2.16/1.00      | ~ v3_tex_2(u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))),sK3)
% 2.16/1.00      | X0_49 != sK3
% 2.16/1.00      | sK0(sK3,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) != u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2755]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_3663,plain,
% 2.16/1.00      ( v3_tex_2(sK0(sK3,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))),sK3)
% 2.16/1.00      | ~ v3_tex_2(u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))),sK3)
% 2.16/1.00      | sK3 != sK3
% 2.16/1.00      | sK0(sK3,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) != u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_3661]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2101,plain,
% 2.16/1.00      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 2.16/1.00      theory(equality) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2773,plain,
% 2.16/1.00      ( sK2(sK3,u1_struct_0(sK4)) != X0_48
% 2.16/1.00      | sK2(sK3,u1_struct_0(sK4)) = u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4))))
% 2.16/1.00      | u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) != X0_48 ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2101]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_3089,plain,
% 2.16/1.00      ( sK2(sK3,u1_struct_0(sK4)) != sK2(sK3,u1_struct_0(sK4))
% 2.16/1.00      | sK2(sK3,u1_struct_0(sK4)) = u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4))))
% 2.16/1.00      | u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) != sK2(sK3,u1_struct_0(sK4)) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2773]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_11,plain,
% 2.16/1.00      ( v2_tex_2(u1_struct_0(X0),X1)
% 2.16/1.00      | ~ m1_pre_topc(X0,X1)
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | ~ v1_tdlat_3(X0)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | ~ l1_pre_topc(X1) ),
% 2.16/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_0,plain,
% 2.16/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.16/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | ~ l1_pre_topc(X1) ),
% 2.16/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_154,plain,
% 2.16/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.16/1.00      | v2_tex_2(u1_struct_0(X0),X1)
% 2.16/1.00      | ~ v1_tdlat_3(X0)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | ~ l1_pre_topc(X1) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_11,c_0]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_155,plain,
% 2.16/1.00      ( v2_tex_2(u1_struct_0(X0),X1)
% 2.16/1.00      | ~ m1_pre_topc(X0,X1)
% 2.16/1.00      | ~ v1_tdlat_3(X0)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | ~ l1_pre_topc(X1) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_154]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_16,plain,
% 2.16/1.00      ( ~ v2_tex_2(X0,X1)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | ~ v3_tdlat_3(X1)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | ~ v2_pre_topc(X1)
% 2.16/1.00      | ~ l1_pre_topc(X1) ),
% 2.16/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_22,negated_conjecture,
% 2.16/1.00      ( v3_tdlat_3(sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_400,plain,
% 2.16/1.00      ( ~ v2_tex_2(X0,X1)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | ~ v2_pre_topc(X1)
% 2.16/1.00      | ~ l1_pre_topc(X1)
% 2.16/1.00      | sK3 != X1 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_401,plain,
% 2.16/1.00      ( ~ v2_tex_2(X0,sK3)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | m1_subset_1(sK2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v2_struct_0(sK3)
% 2.16/1.00      | ~ v2_pre_topc(sK3)
% 2.16/1.00      | ~ l1_pre_topc(sK3) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_400]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_24,negated_conjecture,
% 2.16/1.00      ( ~ v2_struct_0(sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_23,negated_conjecture,
% 2.16/1.00      ( v2_pre_topc(sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_21,negated_conjecture,
% 2.16/1.00      ( l1_pre_topc(sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_405,plain,
% 2.16/1.00      ( m1_subset_1(sK2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ v2_tex_2(X0,sK3) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_401,c_24,c_23,c_21]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_406,plain,
% 2.16/1.00      ( ~ v2_tex_2(X0,sK3)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | m1_subset_1(sK2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_405]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_845,plain,
% 2.16/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.16/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | m1_subset_1(sK2(sK3,X2),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ v1_tdlat_3(X0)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | ~ l1_pre_topc(X1)
% 2.16/1.00      | u1_struct_0(X0) != X2
% 2.16/1.00      | sK3 != X1 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_155,c_406]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_846,plain,
% 2.16/1.00      ( ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | m1_subset_1(sK2(sK3,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ v1_tdlat_3(X0)
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | v2_struct_0(sK3)
% 2.16/1.00      | ~ l1_pre_topc(sK3) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_845]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_850,plain,
% 2.16/1.00      ( ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | m1_subset_1(sK2(sK3,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ v1_tdlat_3(X0)
% 2.16/1.00      | v2_struct_0(X0) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_846,c_24,c_21]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_19,negated_conjecture,
% 2.16/1.00      ( v1_tdlat_3(sK4) ),
% 2.16/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_929,plain,
% 2.16/1.00      ( ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | m1_subset_1(sK2(sK3,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | sK4 != X0 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_850,c_19]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_930,plain,
% 2.16/1.00      ( ~ m1_pre_topc(sK4,sK3)
% 2.16/1.00      | m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v2_struct_0(sK4) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_929]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_20,negated_conjecture,
% 2.16/1.00      ( ~ v2_struct_0(sK4) ),
% 2.16/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_18,negated_conjecture,
% 2.16/1.00      ( m1_pre_topc(sK4,sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_932,plain,
% 2.16/1.00      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_930,c_20,c_18]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_933,plain,
% 2.16/1.00      ( m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_932]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2095,plain,
% 2.16/1.00      ( m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_933]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2359,plain,
% 2.16/1.00      ( m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.16/1.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_2095]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_31,plain,
% 2.16/1.00      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_934,plain,
% 2.16/1.00      ( m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.16/1.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_933]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1222,plain,
% 2.16/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.16/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | sK3 != X1 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_21]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1223,plain,
% 2.16/1.00      ( ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_1222]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2090,plain,
% 2.16/1.00      ( ~ m1_pre_topc(X0_49,sK3)
% 2.16/1.00      | m1_subset_1(u1_struct_0(X0_49),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_1223]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2466,plain,
% 2.16/1.00      ( ~ m1_pre_topc(sK4,sK3)
% 2.16/1.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2090]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2467,plain,
% 2.16/1.00      ( m1_pre_topc(sK4,sK3) != iProver_top
% 2.16/1.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_2466]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2498,plain,
% 2.16/1.00      ( m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_2359,c_31,c_934,c_2467]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_17,negated_conjecture,
% 2.16/1.00      ( ~ v4_tex_2(X0,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | ~ m1_pre_topc(sK4,X0)
% 2.16/1.00      | ~ v1_pre_topc(X0)
% 2.16/1.00      | v2_struct_0(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_9,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | v1_pre_topc(sK1(X1,X0))
% 2.16/1.00      | v1_xboole_0(X0)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | ~ l1_pre_topc(X1) ),
% 2.16/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1138,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | v1_pre_topc(sK1(X1,X0))
% 2.16/1.00      | v1_xboole_0(X0)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | sK3 != X1 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1139,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v1_pre_topc(sK1(sK3,X0))
% 2.16/1.00      | v1_xboole_0(X0)
% 2.16/1.00      | v2_struct_0(sK3) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_1138]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1143,plain,
% 2.16/1.00      ( v1_xboole_0(X0)
% 2.16/1.00      | v1_pre_topc(sK1(sK3,X0))
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_1139,c_24]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1144,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v1_pre_topc(sK1(sK3,X0))
% 2.16/1.00      | v1_xboole_0(X0) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_1143]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1313,plain,
% 2.16/1.00      ( ~ v4_tex_2(X0,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | ~ m1_pre_topc(sK4,X0)
% 2.16/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v1_xboole_0(X1)
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | sK1(sK3,X1) != X0 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_1144]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1314,plain,
% 2.16/1.00      ( ~ v4_tex_2(sK1(sK3,X0),sK3)
% 2.16/1.00      | ~ m1_pre_topc(sK1(sK3,X0),sK3)
% 2.16/1.00      | ~ m1_pre_topc(sK4,sK1(sK3,X0))
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v1_xboole_0(X0)
% 2.16/1.00      | v2_struct_0(sK1(sK3,X0)) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_1313]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_10,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | v1_xboole_0(X0)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | ~ v2_struct_0(sK1(X1,X0))
% 2.16/1.00      | ~ l1_pre_topc(X1) ),
% 2.16/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1117,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | v1_xboole_0(X0)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | ~ v2_struct_0(sK1(X1,X0))
% 2.16/1.00      | sK3 != X1 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1118,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v1_xboole_0(X0)
% 2.16/1.00      | ~ v2_struct_0(sK1(sK3,X0))
% 2.16/1.00      | v2_struct_0(sK3) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_1117]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_8,plain,
% 2.16/1.00      ( m1_pre_topc(sK1(X0,X1),X0)
% 2.16/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.16/1.00      | v1_xboole_0(X1)
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | ~ l1_pre_topc(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1234,plain,
% 2.16/1.00      ( m1_pre_topc(sK1(X0,X1),X0)
% 2.16/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.16/1.00      | v1_xboole_0(X1)
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | sK3 != X0 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1235,plain,
% 2.16/1.00      ( m1_pre_topc(sK1(sK3,X0),sK3)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v1_xboole_0(X0)
% 2.16/1.00      | v2_struct_0(sK3) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_1234]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1318,plain,
% 2.16/1.00      ( v1_xboole_0(X0)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ m1_pre_topc(sK4,sK1(sK3,X0))
% 2.16/1.00      | ~ v4_tex_2(sK1(sK3,X0),sK3) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_1314,c_24,c_1118,c_1235]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1319,plain,
% 2.16/1.00      ( ~ v4_tex_2(sK1(sK3,X0),sK3)
% 2.16/1.00      | ~ m1_pre_topc(sK4,sK1(sK3,X0))
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v1_xboole_0(X0) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_1318]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_13,plain,
% 2.16/1.00      ( ~ v3_tex_2(X0,X1)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | ~ v1_xboole_0(X0)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | ~ v2_pre_topc(X1)
% 2.16/1.00      | ~ l1_pre_topc(X1) ),
% 2.16/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_475,plain,
% 2.16/1.00      ( ~ v3_tex_2(X0,X1)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | ~ v1_xboole_0(X0)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | ~ l1_pre_topc(X1)
% 2.16/1.00      | sK3 != X1 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_476,plain,
% 2.16/1.00      ( ~ v3_tex_2(X0,sK3)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ v1_xboole_0(X0)
% 2.16/1.00      | v2_struct_0(sK3)
% 2.16/1.00      | ~ l1_pre_topc(sK3) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_475]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_480,plain,
% 2.16/1.00      ( ~ v3_tex_2(X0,sK3)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ v1_xboole_0(X0) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_476,c_24,c_21]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1342,plain,
% 2.16/1.00      ( ~ v3_tex_2(X0,sK3)
% 2.16/1.00      | ~ v4_tex_2(sK1(sK3,X0),sK3)
% 2.16/1.00      | ~ m1_pre_topc(sK4,sK1(sK3,X0))
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(resolution,[status(thm)],[c_1319,c_480]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2087,plain,
% 2.16/1.00      ( ~ v3_tex_2(X0_48,sK3)
% 2.16/1.00      | ~ v4_tex_2(sK1(sK3,X0_48),sK3)
% 2.16/1.00      | ~ m1_pre_topc(sK4,sK1(sK3,X0_48))
% 2.16/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_1342]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2367,plain,
% 2.16/1.00      ( v3_tex_2(X0_48,sK3) != iProver_top
% 2.16/1.00      | v4_tex_2(sK1(sK3,X0_48),sK3) != iProver_top
% 2.16/1.00      | m1_pre_topc(sK4,sK1(sK3,X0_48)) != iProver_top
% 2.16/1.00      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_2087]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2989,plain,
% 2.16/1.00      ( v3_tex_2(sK2(sK3,u1_struct_0(sK4)),sK3) != iProver_top
% 2.16/1.00      | v4_tex_2(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3) != iProver_top
% 2.16/1.00      | m1_pre_topc(sK4,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) != iProver_top ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_2498,c_2367]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_14,plain,
% 2.16/1.00      ( ~ v2_tex_2(X0,X1)
% 2.16/1.00      | v3_tex_2(sK2(X1,X0),X1)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | ~ v3_tdlat_3(X1)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | ~ v2_pre_topc(X1)
% 2.16/1.00      | ~ l1_pre_topc(X1) ),
% 2.16/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_442,plain,
% 2.16/1.00      ( ~ v2_tex_2(X0,X1)
% 2.16/1.00      | v3_tex_2(sK2(X1,X0),X1)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | ~ v2_pre_topc(X1)
% 2.16/1.00      | ~ l1_pre_topc(X1)
% 2.16/1.00      | sK3 != X1 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_443,plain,
% 2.16/1.00      ( ~ v2_tex_2(X0,sK3)
% 2.16/1.00      | v3_tex_2(sK2(sK3,X0),sK3)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v2_struct_0(sK3)
% 2.16/1.00      | ~ v2_pre_topc(sK3)
% 2.16/1.00      | ~ l1_pre_topc(sK3) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_442]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_447,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v3_tex_2(sK2(sK3,X0),sK3)
% 2.16/1.00      | ~ v2_tex_2(X0,sK3) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_443,c_24,c_23,c_21]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_448,plain,
% 2.16/1.00      ( ~ v2_tex_2(X0,sK3)
% 2.16/1.00      | v3_tex_2(sK2(sK3,X0),sK3)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_447]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_818,plain,
% 2.16/1.00      ( v3_tex_2(sK2(sK3,X0),sK3)
% 2.16/1.00      | ~ m1_pre_topc(X1,X2)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ v1_tdlat_3(X1)
% 2.16/1.00      | v2_struct_0(X2)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | ~ l1_pre_topc(X2)
% 2.16/1.00      | u1_struct_0(X1) != X0
% 2.16/1.00      | sK3 != X2 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_155,c_448]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_819,plain,
% 2.16/1.00      ( v3_tex_2(sK2(sK3,u1_struct_0(X0)),sK3)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ v1_tdlat_3(X0)
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | v2_struct_0(sK3)
% 2.16/1.00      | ~ l1_pre_topc(sK3) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_818]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_823,plain,
% 2.16/1.00      ( v3_tex_2(sK2(sK3,u1_struct_0(X0)),sK3)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ v1_tdlat_3(X0)
% 2.16/1.00      | v2_struct_0(X0) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_819,c_24,c_21]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_943,plain,
% 2.16/1.00      ( v3_tex_2(sK2(sK3,u1_struct_0(X0)),sK3)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | sK4 != X0 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_823,c_19]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_944,plain,
% 2.16/1.00      ( v3_tex_2(sK2(sK3,u1_struct_0(sK4)),sK3)
% 2.16/1.00      | ~ m1_pre_topc(sK4,sK3)
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v2_struct_0(sK4) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_943]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_946,plain,
% 2.16/1.00      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v3_tex_2(sK2(sK3,u1_struct_0(sK4)),sK3) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_944,c_20,c_18]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_947,plain,
% 2.16/1.00      ( v3_tex_2(sK2(sK3,u1_struct_0(sK4)),sK3)
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_946]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1563,plain,
% 2.16/1.00      ( ~ v4_tex_2(sK1(sK3,X0),sK3)
% 2.16/1.00      | ~ m1_pre_topc(sK4,sK1(sK3,X0))
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | sK2(sK3,u1_struct_0(sK4)) != X0
% 2.16/1.00      | sK3 != sK3 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_1342,c_947]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1564,plain,
% 2.16/1.00      ( ~ v4_tex_2(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
% 2.16/1.00      | ~ m1_pre_topc(sK4,sK1(sK3,sK2(sK3,u1_struct_0(sK4))))
% 2.16/1.00      | ~ m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_1563]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1566,plain,
% 2.16/1.00      ( ~ m1_pre_topc(sK4,sK1(sK3,sK2(sK3,u1_struct_0(sK4))))
% 2.16/1.00      | ~ v4_tex_2(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_1564,c_20,c_18,c_930]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1567,plain,
% 2.16/1.00      ( ~ v4_tex_2(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
% 2.16/1.00      | ~ m1_pre_topc(sK4,sK1(sK3,sK2(sK3,u1_struct_0(sK4))))
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_1566]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1568,plain,
% 2.16/1.00      ( v4_tex_2(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3) != iProver_top
% 2.16/1.00      | m1_pre_topc(sK4,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) != iProver_top
% 2.16/1.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_1567]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_3071,plain,
% 2.16/1.00      ( v4_tex_2(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3) != iProver_top
% 2.16/1.00      | m1_pre_topc(sK4,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) != iProver_top ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_2989,c_31,c_1568,c_2467]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_3073,plain,
% 2.16/1.00      ( ~ v4_tex_2(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
% 2.16/1.00      | ~ m1_pre_topc(sK4,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) ),
% 2.16/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3071]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2521,plain,
% 2.16/1.00      ( v3_tex_2(X0_48,X0_49)
% 2.16/1.00      | ~ v3_tex_2(sK2(sK3,u1_struct_0(sK4)),sK3)
% 2.16/1.00      | X0_49 != sK3
% 2.16/1.00      | X0_48 != sK2(sK3,u1_struct_0(sK4)) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2108]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2662,plain,
% 2.16/1.00      ( ~ v3_tex_2(sK2(sK3,u1_struct_0(sK4)),sK3)
% 2.16/1.00      | v3_tex_2(u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))),X0_49)
% 2.16/1.00      | X0_49 != sK3
% 2.16/1.00      | u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) != sK2(sK3,u1_struct_0(sK4)) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2521]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2664,plain,
% 2.16/1.00      ( ~ v3_tex_2(sK2(sK3,u1_struct_0(sK4)),sK3)
% 2.16/1.00      | v3_tex_2(u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))),sK3)
% 2.16/1.00      | sK3 != sK3
% 2.16/1.00      | u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) != sK2(sK3,u1_struct_0(sK4)) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2662]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2098,plain,( X0_48 = X0_48 ),theory(equality) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2650,plain,
% 2.16/1.00      ( sK2(sK3,u1_struct_0(sK4)) = sK2(sK3,u1_struct_0(sK4)) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2098]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2635,plain,
% 2.16/1.00      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2098]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2,plain,
% 2.16/1.00      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.16/1.00      | ~ m1_pre_topc(X0,X2)
% 2.16/1.00      | ~ m1_pre_topc(X1,X2)
% 2.16/1.00      | m1_pre_topc(X0,X1)
% 2.16/1.00      | ~ v2_pre_topc(X2)
% 2.16/1.00      | ~ l1_pre_topc(X2) ),
% 2.16/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_496,plain,
% 2.16/1.00      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.16/1.00      | ~ m1_pre_topc(X0,X2)
% 2.16/1.00      | ~ m1_pre_topc(X1,X2)
% 2.16/1.00      | m1_pre_topc(X0,X1)
% 2.16/1.00      | ~ l1_pre_topc(X2)
% 2.16/1.00      | sK3 != X2 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_23]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_497,plain,
% 2.16/1.00      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.16/1.00      | m1_pre_topc(X0,X1)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X1,sK3)
% 2.16/1.00      | ~ l1_pre_topc(sK3) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_496]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_499,plain,
% 2.16/1.00      ( ~ m1_pre_topc(X1,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | m1_pre_topc(X0,X1)
% 2.16/1.00      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_497,c_21]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_500,plain,
% 2.16/1.00      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.16/1.00      | m1_pre_topc(X0,X1)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X1,sK3) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_499]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_15,plain,
% 2.16/1.00      ( ~ v2_tex_2(X0,X1)
% 2.16/1.00      | r1_tarski(X0,sK2(X1,X0))
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | ~ v3_tdlat_3(X1)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | ~ v2_pre_topc(X1)
% 2.16/1.00      | ~ l1_pre_topc(X1) ),
% 2.16/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_421,plain,
% 2.16/1.00      ( ~ v2_tex_2(X0,X1)
% 2.16/1.00      | r1_tarski(X0,sK2(X1,X0))
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | ~ v2_pre_topc(X1)
% 2.16/1.00      | ~ l1_pre_topc(X1)
% 2.16/1.00      | sK3 != X1 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_422,plain,
% 2.16/1.00      ( ~ v2_tex_2(X0,sK3)
% 2.16/1.00      | r1_tarski(X0,sK2(sK3,X0))
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v2_struct_0(sK3)
% 2.16/1.00      | ~ v2_pre_topc(sK3)
% 2.16/1.00      | ~ l1_pre_topc(sK3) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_421]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_426,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | r1_tarski(X0,sK2(sK3,X0))
% 2.16/1.00      | ~ v2_tex_2(X0,sK3) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_422,c_24,c_23,c_21]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_427,plain,
% 2.16/1.00      ( ~ v2_tex_2(X0,sK3)
% 2.16/1.00      | r1_tarski(X0,sK2(sK3,X0))
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_426]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_555,plain,
% 2.16/1.00      ( ~ v2_tex_2(X0,sK3)
% 2.16/1.00      | m1_pre_topc(X1,X2)
% 2.16/1.00      | ~ m1_pre_topc(X1,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X2,sK3)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | sK2(sK3,X0) != u1_struct_0(X2)
% 2.16/1.00      | u1_struct_0(X1) != X0 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_500,c_427]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_556,plain,
% 2.16/1.00      ( ~ v2_tex_2(u1_struct_0(X0),sK3)
% 2.16/1.00      | m1_pre_topc(X0,X1)
% 2.16/1.00      | ~ m1_pre_topc(X1,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | sK2(sK3,u1_struct_0(X0)) != u1_struct_0(X1) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_555]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_872,plain,
% 2.16/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.16/1.00      | m1_pre_topc(X2,X3)
% 2.16/1.00      | ~ m1_pre_topc(X2,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X3,sK3)
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ v1_tdlat_3(X0)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | ~ l1_pre_topc(X1)
% 2.16/1.00      | sK2(sK3,u1_struct_0(X2)) != u1_struct_0(X3)
% 2.16/1.00      | u1_struct_0(X2) != u1_struct_0(X0)
% 2.16/1.00      | sK3 != X1 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_155,c_556]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_873,plain,
% 2.16/1.00      ( m1_pre_topc(X0,X1)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X2,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X1,sK3)
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ v1_tdlat_3(X2)
% 2.16/1.00      | v2_struct_0(X2)
% 2.16/1.00      | v2_struct_0(sK3)
% 2.16/1.00      | ~ l1_pre_topc(sK3)
% 2.16/1.00      | sK2(sK3,u1_struct_0(X0)) != u1_struct_0(X1)
% 2.16/1.00      | u1_struct_0(X0) != u1_struct_0(X2) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_872]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_875,plain,
% 2.16/1.00      ( m1_pre_topc(X0,X1)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X2,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X1,sK3)
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ v1_tdlat_3(X2)
% 2.16/1.00      | v2_struct_0(X2)
% 2.16/1.00      | sK2(sK3,u1_struct_0(X0)) != u1_struct_0(X1)
% 2.16/1.00      | u1_struct_0(X0) != u1_struct_0(X2) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_873,c_24,c_21]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_876,plain,
% 2.16/1.00      ( m1_pre_topc(X0,X1)
% 2.16/1.00      | ~ m1_pre_topc(X2,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X1,sK3)
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ v1_tdlat_3(X2)
% 2.16/1.00      | v2_struct_0(X2)
% 2.16/1.00      | sK2(sK3,u1_struct_0(X0)) != u1_struct_0(X1)
% 2.16/1.00      | u1_struct_0(X0) != u1_struct_0(X2) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_875]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_957,plain,
% 2.16/1.00      ( m1_pre_topc(X0,X1)
% 2.16/1.00      | ~ m1_pre_topc(X1,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X2,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v2_struct_0(X2)
% 2.16/1.00      | sK2(sK3,u1_struct_0(X0)) != u1_struct_0(X1)
% 2.16/1.00      | u1_struct_0(X0) != u1_struct_0(X2)
% 2.16/1.00      | sK4 != X2 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_876]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_958,plain,
% 2.16/1.00      ( m1_pre_topc(X0,X1)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X1,sK3)
% 2.16/1.00      | ~ m1_pre_topc(sK4,sK3)
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v2_struct_0(sK4)
% 2.16/1.00      | sK2(sK3,u1_struct_0(X0)) != u1_struct_0(X1)
% 2.16/1.00      | u1_struct_0(X0) != u1_struct_0(sK4) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_957]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_960,plain,
% 2.16/1.00      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | m1_pre_topc(X0,X1)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X1,sK3)
% 2.16/1.00      | sK2(sK3,u1_struct_0(X0)) != u1_struct_0(X1)
% 2.16/1.00      | u1_struct_0(X0) != u1_struct_0(sK4) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_958,c_20,c_18]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_961,plain,
% 2.16/1.00      ( m1_pre_topc(X0,X1)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X1,sK3)
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | sK2(sK3,u1_struct_0(X0)) != u1_struct_0(X1)
% 2.16/1.00      | u1_struct_0(X0) != u1_struct_0(sK4) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_960]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1302,plain,
% 2.16/1.00      ( m1_pre_topc(X0,X1)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X1,sK3)
% 2.16/1.00      | sK2(sK3,u1_struct_0(X0)) != u1_struct_0(X1)
% 2.16/1.00      | u1_struct_0(X0) != u1_struct_0(sK4) ),
% 2.16/1.00      inference(backward_subsumption_resolution,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_1223,c_961]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2088,plain,
% 2.16/1.00      ( m1_pre_topc(X0_49,X1_49)
% 2.16/1.00      | ~ m1_pre_topc(X0_49,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X1_49,sK3)
% 2.16/1.00      | sK2(sK3,u1_struct_0(X0_49)) != u1_struct_0(X1_49)
% 2.16/1.00      | u1_struct_0(X0_49) != u1_struct_0(sK4) ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_1302]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2483,plain,
% 2.16/1.00      ( ~ m1_pre_topc(X0_49,sK3)
% 2.16/1.00      | m1_pre_topc(sK4,X0_49)
% 2.16/1.00      | ~ m1_pre_topc(sK4,sK3)
% 2.16/1.00      | sK2(sK3,u1_struct_0(sK4)) != u1_struct_0(X0_49)
% 2.16/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2088]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2617,plain,
% 2.16/1.00      ( ~ m1_pre_topc(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
% 2.16/1.00      | m1_pre_topc(sK4,sK1(sK3,sK2(sK3,u1_struct_0(sK4))))
% 2.16/1.00      | ~ m1_pre_topc(sK4,sK3)
% 2.16/1.00      | sK2(sK3,u1_struct_0(sK4)) != u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4))))
% 2.16/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2483]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_4,plain,
% 2.16/1.00      ( v4_tex_2(X0,X1)
% 2.16/1.00      | ~ m1_pre_topc(X0,X1)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | ~ l1_pre_topc(X1)
% 2.16/1.00      | sK0(X1,X0) = u1_struct_0(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1201,plain,
% 2.16/1.00      ( v4_tex_2(X0,X1)
% 2.16/1.00      | ~ m1_pre_topc(X0,X1)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | sK0(X1,X0) = u1_struct_0(X0)
% 2.16/1.00      | sK3 != X1 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_21]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1202,plain,
% 2.16/1.00      ( v4_tex_2(X0,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | v2_struct_0(sK3)
% 2.16/1.00      | sK0(sK3,X0) = u1_struct_0(X0) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_1201]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1206,plain,
% 2.16/1.00      ( ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | v4_tex_2(X0,sK3)
% 2.16/1.00      | sK0(sK3,X0) = u1_struct_0(X0) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_1202,c_24]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1207,plain,
% 2.16/1.00      ( v4_tex_2(X0,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | sK0(sK3,X0) = u1_struct_0(X0) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_1206]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2091,plain,
% 2.16/1.00      ( v4_tex_2(X0_49,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X0_49,sK3)
% 2.16/1.00      | sK0(sK3,X0_49) = u1_struct_0(X0_49) ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_1207]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2557,plain,
% 2.16/1.00      ( v4_tex_2(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
% 2.16/1.00      | ~ m1_pre_topc(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
% 2.16/1.00      | sK0(sK3,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) = u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2091]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_3,plain,
% 2.16/1.00      ( ~ v3_tex_2(sK0(X0,X1),X0)
% 2.16/1.00      | v4_tex_2(X1,X0)
% 2.16/1.00      | ~ m1_pre_topc(X1,X0)
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | ~ l1_pre_topc(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1255,plain,
% 2.16/1.00      ( ~ v3_tex_2(sK0(X0,X1),X0)
% 2.16/1.00      | v4_tex_2(X1,X0)
% 2.16/1.00      | ~ m1_pre_topc(X1,X0)
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | sK3 != X0 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_21]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1256,plain,
% 2.16/1.00      ( ~ v3_tex_2(sK0(sK3,X0),sK3)
% 2.16/1.00      | v4_tex_2(X0,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | v2_struct_0(sK3) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_1255]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1260,plain,
% 2.16/1.00      ( ~ m1_pre_topc(X0,sK3)
% 2.16/1.00      | v4_tex_2(X0,sK3)
% 2.16/1.00      | ~ v3_tex_2(sK0(sK3,X0),sK3) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_1256,c_24]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1261,plain,
% 2.16/1.00      ( ~ v3_tex_2(sK0(sK3,X0),sK3)
% 2.16/1.00      | v4_tex_2(X0,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X0,sK3) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_1260]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2089,plain,
% 2.16/1.00      ( ~ v3_tex_2(sK0(sK3,X0_49),sK3)
% 2.16/1.00      | v4_tex_2(X0_49,sK3)
% 2.16/1.00      | ~ m1_pre_topc(X0_49,sK3) ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_1261]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2559,plain,
% 2.16/1.00      ( ~ v3_tex_2(sK0(sK3,sK1(sK3,sK2(sK3,u1_struct_0(sK4)))),sK3)
% 2.16/1.00      | v4_tex_2(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
% 2.16/1.00      | ~ m1_pre_topc(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2089]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_7,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | v1_xboole_0(X0)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | ~ l1_pre_topc(X1)
% 2.16/1.00      | u1_struct_0(sK1(X1,X0)) = X0 ),
% 2.16/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1159,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.00      | v1_xboole_0(X0)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | u1_struct_0(sK1(X1,X0)) = X0
% 2.16/1.00      | sK3 != X1 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1160,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v1_xboole_0(X0)
% 2.16/1.00      | v2_struct_0(sK3)
% 2.16/1.00      | u1_struct_0(sK1(sK3,X0)) = X0 ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_1159]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1164,plain,
% 2.16/1.00      ( v1_xboole_0(X0)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | u1_struct_0(sK1(sK3,X0)) = X0 ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_1160,c_24]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1165,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v1_xboole_0(X0)
% 2.16/1.00      | u1_struct_0(sK1(sK3,X0)) = X0 ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_1164]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1373,plain,
% 2.16/1.00      ( ~ v3_tex_2(X0,sK3)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | u1_struct_0(sK1(sK3,X0)) = X0 ),
% 2.16/1.00      inference(resolution,[status(thm)],[c_1165,c_480]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2085,plain,
% 2.16/1.00      ( ~ v3_tex_2(X0_48,sK3)
% 2.16/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | u1_struct_0(sK1(sK3,X0_48)) = X0_48 ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_1373]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2513,plain,
% 2.16/1.00      ( ~ v3_tex_2(sK2(sK3,u1_struct_0(sK4)),sK3)
% 2.16/1.00      | ~ m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | u1_struct_0(sK1(sK3,sK2(sK3,u1_struct_0(sK4)))) = sK2(sK3,u1_struct_0(sK4)) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2085]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2099,plain,( X0_49 = X0_49 ),theory(equality) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2122,plain,
% 2.16/1.00      ( sK3 = sK3 ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2099]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1239,plain,
% 2.16/1.00      ( v1_xboole_0(X0)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | m1_pre_topc(sK1(sK3,X0),sK3) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_1235,c_24]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1240,plain,
% 2.16/1.00      ( m1_pre_topc(sK1(sK3,X0),sK3)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | v1_xboole_0(X0) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_1239]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1359,plain,
% 2.16/1.00      ( ~ v3_tex_2(X0,sK3)
% 2.16/1.00      | m1_pre_topc(sK1(sK3,X0),sK3)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(resolution,[status(thm)],[c_1240,c_480]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1549,plain,
% 2.16/1.00      ( m1_pre_topc(sK1(sK3,X0),sK3)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | sK2(sK3,u1_struct_0(sK4)) != X0
% 2.16/1.00      | sK3 != sK3 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_1359,c_947]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1550,plain,
% 2.16/1.00      ( m1_pre_topc(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
% 2.16/1.00      | ~ m1_subset_1(sK2(sK3,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_1549]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1552,plain,
% 2.16/1.00      ( m1_pre_topc(sK1(sK3,sK2(sK3,u1_struct_0(sK4))),sK3)
% 2.16/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_1550,c_20,c_18,c_930]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(contradiction,plain,
% 2.16/1.00      ( $false ),
% 2.16/1.00      inference(minisat,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_3663,c_3089,c_3073,c_2664,c_2650,c_2635,c_2617,c_2557,
% 2.16/1.00                 c_2559,c_2513,c_2466,c_2122,c_1552,c_947,c_933,c_18]) ).
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  ------                               Statistics
% 2.16/1.00  
% 2.16/1.00  ------ General
% 2.16/1.00  
% 2.16/1.00  abstr_ref_over_cycles:                  0
% 2.16/1.00  abstr_ref_under_cycles:                 0
% 2.16/1.00  gc_basic_clause_elim:                   0
% 2.16/1.00  forced_gc_time:                         0
% 2.16/1.00  parsing_time:                           0.009
% 2.16/1.00  unif_index_cands_time:                  0.
% 2.16/1.00  unif_index_add_time:                    0.
% 2.16/1.00  orderings_time:                         0.
% 2.16/1.00  out_proof_time:                         0.011
% 2.16/1.00  total_time:                             0.142
% 2.16/1.00  num_of_symbols:                         51
% 2.16/1.00  num_of_terms:                           2070
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing
% 2.16/1.00  
% 2.16/1.00  num_of_splits:                          0
% 2.16/1.00  num_of_split_atoms:                     0
% 2.16/1.00  num_of_reused_defs:                     0
% 2.16/1.00  num_eq_ax_congr_red:                    14
% 2.16/1.00  num_of_sem_filtered_clauses:            1
% 2.16/1.00  num_of_subtypes:                        3
% 2.16/1.00  monotx_restored_types:                  0
% 2.16/1.00  sat_num_of_epr_types:                   0
% 2.16/1.00  sat_num_of_non_cyclic_types:            0
% 2.16/1.00  sat_guarded_non_collapsed_types:        1
% 2.16/1.00  num_pure_diseq_elim:                    0
% 2.16/1.00  simp_replaced_by:                       0
% 2.16/1.00  res_preprocessed:                       88
% 2.16/1.00  prep_upred:                             0
% 2.16/1.00  prep_unflattend:                        56
% 2.16/1.00  smt_new_axioms:                         0
% 2.16/1.00  pred_elim_cands:                        4
% 2.16/1.00  pred_elim:                              9
% 2.16/1.00  pred_elim_cl:                           13
% 2.16/1.00  pred_elim_cycles:                       18
% 2.16/1.00  merged_defs:                            0
% 2.16/1.00  merged_defs_ncl:                        0
% 2.16/1.00  bin_hyper_res:                          0
% 2.16/1.00  prep_cycles:                            4
% 2.16/1.00  pred_elim_time:                         0.047
% 2.16/1.00  splitting_time:                         0.
% 2.16/1.00  sem_filter_time:                        0.
% 2.16/1.00  monotx_time:                            0.
% 2.16/1.00  subtype_inf_time:                       0.
% 2.16/1.00  
% 2.16/1.00  ------ Problem properties
% 2.16/1.00  
% 2.16/1.00  clauses:                                12
% 2.16/1.00  conjectures:                            1
% 2.16/1.00  epr:                                    1
% 2.16/1.00  horn:                                   10
% 2.16/1.00  ground:                                 3
% 2.16/1.00  unary:                                  1
% 2.16/1.00  binary:                                 3
% 2.16/1.00  lits:                                   34
% 2.16/1.00  lits_eq:                                4
% 2.16/1.00  fd_pure:                                0
% 2.16/1.00  fd_pseudo:                              0
% 2.16/1.00  fd_cond:                                0
% 2.16/1.00  fd_pseudo_cond:                         0
% 2.16/1.00  ac_symbols:                             0
% 2.16/1.00  
% 2.16/1.00  ------ Propositional Solver
% 2.16/1.00  
% 2.16/1.00  prop_solver_calls:                      27
% 2.16/1.00  prop_fast_solver_calls:                 1171
% 2.16/1.00  smt_solver_calls:                       0
% 2.16/1.00  smt_fast_solver_calls:                  0
% 2.16/1.00  prop_num_of_clauses:                    921
% 2.16/1.00  prop_preprocess_simplified:             3448
% 2.16/1.00  prop_fo_subsumed:                       80
% 2.16/1.00  prop_solver_time:                       0.
% 2.16/1.00  smt_solver_time:                        0.
% 2.16/1.00  smt_fast_solver_time:                   0.
% 2.16/1.00  prop_fast_solver_time:                  0.
% 2.16/1.00  prop_unsat_core_time:                   0.
% 2.16/1.00  
% 2.16/1.00  ------ QBF
% 2.16/1.00  
% 2.16/1.00  qbf_q_res:                              0
% 2.16/1.00  qbf_num_tautologies:                    0
% 2.16/1.00  qbf_prep_cycles:                        0
% 2.16/1.00  
% 2.16/1.00  ------ BMC1
% 2.16/1.00  
% 2.16/1.00  bmc1_current_bound:                     -1
% 2.16/1.00  bmc1_last_solved_bound:                 -1
% 2.16/1.00  bmc1_unsat_core_size:                   -1
% 2.16/1.00  bmc1_unsat_core_parents_size:           -1
% 2.16/1.00  bmc1_merge_next_fun:                    0
% 2.16/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.16/1.00  
% 2.16/1.00  ------ Instantiation
% 2.16/1.00  
% 2.16/1.00  inst_num_of_clauses:                    173
% 2.16/1.00  inst_num_in_passive:                    54
% 2.16/1.00  inst_num_in_active:                     112
% 2.16/1.00  inst_num_in_unprocessed:                6
% 2.16/1.00  inst_num_of_loops:                      140
% 2.16/1.00  inst_num_of_learning_restarts:          0
% 2.16/1.00  inst_num_moves_active_passive:          23
% 2.16/1.00  inst_lit_activity:                      0
% 2.16/1.00  inst_lit_activity_moves:                0
% 2.16/1.00  inst_num_tautologies:                   0
% 2.16/1.00  inst_num_prop_implied:                  0
% 2.16/1.00  inst_num_existing_simplified:           0
% 2.16/1.00  inst_num_eq_res_simplified:             0
% 2.16/1.00  inst_num_child_elim:                    0
% 2.16/1.00  inst_num_of_dismatching_blockings:      12
% 2.16/1.00  inst_num_of_non_proper_insts:           134
% 2.16/1.00  inst_num_of_duplicates:                 0
% 2.16/1.00  inst_inst_num_from_inst_to_res:         0
% 2.16/1.00  inst_dismatching_checking_time:         0.
% 2.16/1.00  
% 2.16/1.00  ------ Resolution
% 2.16/1.00  
% 2.16/1.00  res_num_of_clauses:                     0
% 2.16/1.00  res_num_in_passive:                     0
% 2.16/1.00  res_num_in_active:                      0
% 2.16/1.00  res_num_of_loops:                       92
% 2.16/1.00  res_forward_subset_subsumed:            12
% 2.16/1.00  res_backward_subset_subsumed:           0
% 2.16/1.00  res_forward_subsumed:                   0
% 2.16/1.00  res_backward_subsumed:                  0
% 2.16/1.00  res_forward_subsumption_resolution:     1
% 2.16/1.00  res_backward_subsumption_resolution:    1
% 2.16/1.00  res_clause_to_clause_subsumption:       135
% 2.16/1.00  res_orphan_elimination:                 0
% 2.16/1.00  res_tautology_del:                      28
% 2.16/1.00  res_num_eq_res_simplified:              0
% 2.16/1.00  res_num_sel_changes:                    0
% 2.16/1.00  res_moves_from_active_to_pass:          0
% 2.16/1.00  
% 2.16/1.00  ------ Superposition
% 2.16/1.00  
% 2.16/1.00  sup_time_total:                         0.
% 2.16/1.00  sup_time_generating:                    0.
% 2.16/1.00  sup_time_sim_full:                      0.
% 2.16/1.00  sup_time_sim_immed:                     0.
% 2.16/1.00  
% 2.16/1.00  sup_num_of_clauses:                     52
% 2.16/1.00  sup_num_in_active:                      26
% 2.16/1.00  sup_num_in_passive:                     26
% 2.16/1.00  sup_num_of_loops:                       26
% 2.16/1.00  sup_fw_superposition:                   20
% 2.16/1.00  sup_bw_superposition:                   29
% 2.16/1.00  sup_immediate_simplified:               13
% 2.16/1.00  sup_given_eliminated:                   0
% 2.16/1.00  comparisons_done:                       0
% 2.16/1.00  comparisons_avoided:                    3
% 2.16/1.00  
% 2.16/1.00  ------ Simplifications
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  sim_fw_subset_subsumed:                 4
% 2.16/1.00  sim_bw_subset_subsumed:                 0
% 2.16/1.00  sim_fw_subsumed:                        2
% 2.16/1.00  sim_bw_subsumed:                        0
% 2.16/1.00  sim_fw_subsumption_res:                 1
% 2.16/1.00  sim_bw_subsumption_res:                 0
% 2.16/1.00  sim_tautology_del:                      3
% 2.16/1.00  sim_eq_tautology_del:                   1
% 2.16/1.00  sim_eq_res_simp:                        1
% 2.16/1.00  sim_fw_demodulated:                     0
% 2.16/1.00  sim_bw_demodulated:                     0
% 2.16/1.00  sim_light_normalised:                   7
% 2.16/1.00  sim_joinable_taut:                      0
% 2.16/1.00  sim_joinable_simp:                      0
% 2.16/1.00  sim_ac_normalised:                      0
% 2.16/1.00  sim_smt_subsumption:                    0
% 2.16/1.00  
%------------------------------------------------------------------------------
