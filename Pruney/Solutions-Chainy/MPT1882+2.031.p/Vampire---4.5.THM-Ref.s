%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:04 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :  115 (2043 expanded)
%              Number of leaves         :   11 ( 533 expanded)
%              Depth                    :   27
%              Number of atoms          :  515 (18006 expanded)
%              Number of equality atoms :   34 ( 233 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f470,plain,(
    $false ),
    inference(resolution,[],[f451,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f451,plain,(
    ! [X0] : ~ r1_tarski(k1_tarski(X0),k1_tarski(sK3(sK1))) ),
    inference(resolution,[],[f440,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f440,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_tarski(sK3(sK1))) ),
    inference(resolution,[],[f439,f56])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f439,plain,(
    v1_xboole_0(k1_tarski(sK3(sK1))) ),
    inference(subsumption_resolution,[],[f437,f244])).

fof(f244,plain,(
    r1_tarski(sK1,sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f243,f175])).

fof(f175,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f133,f129])).

fof(f129,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f128,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v3_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v3_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v3_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v3_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v3_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

fof(f128,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v1_zfmisc_1(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f127,f39])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f127,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v1_zfmisc_1(sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f126,f40])).

fof(f40,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f126,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v1_zfmisc_1(sK1)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f125,f41])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f125,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v1_zfmisc_1(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f112,f42])).

fof(f42,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f112,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f43,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_zfmisc_1(X1) )
            & ( v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f133,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f132,f41])).

fof(f132,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f130,f43])).

fof(f130,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f44,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f44,plain,
    ( v3_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f243,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f146,f176])).

fof(f176,plain,(
    v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f175,f124])).

fof(f124,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f123,f38])).

fof(f123,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f122,f39])).

fof(f122,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f121,f40])).

fof(f121,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f120,f41])).

fof(f120,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f111,f42])).

fof(f111,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f43,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f146,plain,
    ( ~ v1_zfmisc_1(sK1)
    | r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f145,f41])).

fof(f145,plain,
    ( ~ v1_zfmisc_1(sK1)
    | r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f139,f43])).

fof(f139,plain,
    ( ~ v1_zfmisc_1(sK1)
    | r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f45,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f437,plain,
    ( ~ r1_tarski(sK1,sK2(sK0,sK1))
    | v1_xboole_0(k1_tarski(sK3(sK1))) ),
    inference(superposition,[],[f394,f255])).

fof(f255,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | v1_xboole_0(k1_tarski(sK3(sK1))) ),
    inference(resolution,[],[f102,f208])).

fof(f208,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK1)
      | sK1 = X3
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f99,f176])).

% (4554)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f99,plain,(
    ! [X3] :
      ( sK1 = X3
      | ~ r1_tarski(X3,sK1)
      | ~ v1_zfmisc_1(sK1)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f42,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f102,plain,(
    r1_tarski(k1_tarski(sK3(sK1)),sK1) ),
    inference(resolution,[],[f95,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f95,plain,(
    r2_hidden(sK3(sK1),sK1) ),
    inference(resolution,[],[f42,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f394,plain,(
    ! [X0] : ~ r1_tarski(k1_tarski(X0),sK2(sK0,sK1)) ),
    inference(resolution,[],[f392,f61])).

fof(f392,plain,(
    ! [X0] : ~ r2_hidden(X0,sK2(sK0,sK1)) ),
    inference(resolution,[],[f391,f56])).

fof(f391,plain,(
    v1_xboole_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f390,f282])).

fof(f282,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f271,f213])).

fof(f213,plain,(
    v2_tex_2(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f212,f175])).

fof(f212,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f144,f176])).

fof(f144,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f143,f41])).

fof(f143,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f138,f43])).

fof(f138,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f45,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f271,plain,
    ( ~ v2_tex_2(sK2(sK0,sK1),sK0)
    | v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f269,f91])).

fof(f91,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X7,sK0)
      | v1_zfmisc_1(X7)
      | v1_xboole_0(X7) ) ),
    inference(subsumption_resolution,[],[f90,f38])).

fof(f90,plain,(
    ! [X7] :
      ( v1_zfmisc_1(X7)
      | ~ v2_tex_2(X7,sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X7)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f89,f39])).

fof(f89,plain,(
    ! [X7] :
      ( v1_zfmisc_1(X7)
      | ~ v2_tex_2(X7,sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X7)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f87,f40])).

fof(f87,plain,(
    ! [X7] :
      ( v1_zfmisc_1(X7)
      | ~ v2_tex_2(X7,sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X7)
      | ~ v2_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f41,f54])).

fof(f269,plain,(
    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f268,f175])).

fof(f268,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f142,f176])).

fof(f142,plain,
    ( ~ v1_zfmisc_1(sK1)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f141,f41])).

fof(f141,plain,
    ( ~ v1_zfmisc_1(sK1)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f137,f43])).

fof(f137,plain,
    ( ~ v1_zfmisc_1(sK1)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f45,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f390,plain,
    ( ~ v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f249,f252])).

fof(f252,plain,(
    sK1 != sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f251,f175])).

fof(f251,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f148,f176])).

fof(f148,plain,
    ( ~ v1_zfmisc_1(sK1)
    | sK1 != sK2(sK0,sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f147,f41])).

fof(f147,plain,
    ( ~ v1_zfmisc_1(sK1)
    | sK1 != sK2(sK0,sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f140,f43])).

fof(f140,plain,
    ( ~ v1_zfmisc_1(sK1)
    | sK1 != sK2(sK0,sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f45,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK2(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f249,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f244,f98])).

fof(f98,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK1,X2)
      | sK1 = X2
      | ~ v1_zfmisc_1(X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f42,f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:36:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (1214349313)
% 0.13/0.37  ipcrm: permission denied for id (1217921026)
% 0.13/0.37  ipcrm: permission denied for id (1217953795)
% 0.13/0.37  ipcrm: permission denied for id (1218019333)
% 0.13/0.37  ipcrm: permission denied for id (1214513158)
% 0.13/0.38  ipcrm: permission denied for id (1218052103)
% 0.13/0.38  ipcrm: permission denied for id (1218215948)
% 0.13/0.38  ipcrm: permission denied for id (1214709773)
% 0.13/0.38  ipcrm: permission denied for id (1214742542)
% 0.13/0.39  ipcrm: permission denied for id (1218248719)
% 0.13/0.39  ipcrm: permission denied for id (1218281488)
% 0.13/0.39  ipcrm: permission denied for id (1218347026)
% 0.13/0.39  ipcrm: permission denied for id (1218379795)
% 0.13/0.39  ipcrm: permission denied for id (1218445333)
% 0.13/0.39  ipcrm: permission denied for id (1214939158)
% 0.13/0.40  ipcrm: permission denied for id (1218478103)
% 0.13/0.40  ipcrm: permission denied for id (1218510872)
% 0.13/0.40  ipcrm: permission denied for id (1215070234)
% 0.13/0.40  ipcrm: permission denied for id (1218576411)
% 0.13/0.40  ipcrm: permission denied for id (1215103004)
% 0.13/0.40  ipcrm: permission denied for id (1218609181)
% 0.13/0.40  ipcrm: permission denied for id (1218674719)
% 0.21/0.41  ipcrm: permission denied for id (1215234080)
% 0.21/0.41  ipcrm: permission denied for id (1218707489)
% 0.21/0.41  ipcrm: permission denied for id (1218740258)
% 0.21/0.41  ipcrm: permission denied for id (1215365158)
% 0.21/0.41  ipcrm: permission denied for id (1218871335)
% 0.21/0.42  ipcrm: permission denied for id (1218904104)
% 0.21/0.42  ipcrm: permission denied for id (1218936873)
% 0.21/0.42  ipcrm: permission denied for id (1218969642)
% 0.21/0.42  ipcrm: permission denied for id (1215463467)
% 0.21/0.42  ipcrm: permission denied for id (1215561774)
% 0.21/0.43  ipcrm: permission denied for id (1219133488)
% 0.21/0.43  ipcrm: permission denied for id (1215692850)
% 0.21/0.43  ipcrm: permission denied for id (1215725619)
% 0.21/0.43  ipcrm: permission denied for id (1215823927)
% 0.21/0.43  ipcrm: permission denied for id (1215856696)
% 0.21/0.44  ipcrm: permission denied for id (1219297337)
% 0.21/0.44  ipcrm: permission denied for id (1219330106)
% 0.21/0.44  ipcrm: permission denied for id (1215955003)
% 0.21/0.44  ipcrm: permission denied for id (1215987772)
% 0.21/0.44  ipcrm: permission denied for id (1216020542)
% 0.21/0.45  ipcrm: permission denied for id (1216118849)
% 0.21/0.45  ipcrm: permission denied for id (1216151618)
% 0.21/0.45  ipcrm: permission denied for id (1216184387)
% 0.21/0.45  ipcrm: permission denied for id (1216249925)
% 0.21/0.45  ipcrm: permission denied for id (1216282694)
% 0.21/0.45  ipcrm: permission denied for id (1216315463)
% 0.21/0.45  ipcrm: permission denied for id (1219526728)
% 0.21/0.45  ipcrm: permission denied for id (1219559497)
% 0.21/0.46  ipcrm: permission denied for id (1219625035)
% 0.21/0.46  ipcrm: permission denied for id (1216413772)
% 0.21/0.46  ipcrm: permission denied for id (1216446541)
% 0.21/0.46  ipcrm: permission denied for id (1216577617)
% 0.21/0.47  ipcrm: permission denied for id (1216643155)
% 0.21/0.47  ipcrm: permission denied for id (1219788884)
% 0.21/0.47  ipcrm: permission denied for id (1219919960)
% 0.21/0.47  ipcrm: permission denied for id (1219952729)
% 0.21/0.47  ipcrm: permission denied for id (1219985498)
% 0.21/0.48  ipcrm: permission denied for id (1216872539)
% 0.21/0.48  ipcrm: permission denied for id (1220083806)
% 0.21/0.48  ipcrm: permission denied for id (1216970847)
% 0.21/0.48  ipcrm: permission denied for id (1217003616)
% 0.21/0.48  ipcrm: permission denied for id (1220116577)
% 0.21/0.48  ipcrm: permission denied for id (1220149346)
% 0.21/0.49  ipcrm: permission denied for id (1220182115)
% 0.21/0.49  ipcrm: permission denied for id (1217101924)
% 0.21/0.49  ipcrm: permission denied for id (1220280423)
% 0.21/0.49  ipcrm: permission denied for id (1217298539)
% 0.21/0.50  ipcrm: permission denied for id (1217331308)
% 0.21/0.50  ipcrm: permission denied for id (1217364077)
% 0.21/0.50  ipcrm: permission denied for id (1217396846)
% 0.21/0.50  ipcrm: permission denied for id (1220411503)
% 0.21/0.50  ipcrm: permission denied for id (1217495154)
% 0.21/0.51  ipcrm: permission denied for id (1220608118)
% 0.21/0.51  ipcrm: permission denied for id (1217626231)
% 0.21/0.51  ipcrm: permission denied for id (1220640888)
% 0.21/0.51  ipcrm: permission denied for id (1217691769)
% 0.21/0.51  ipcrm: permission denied for id (1217724538)
% 0.21/0.52  ipcrm: permission denied for id (1217790076)
% 0.21/0.52  ipcrm: permission denied for id (1217822845)
% 0.21/0.52  ipcrm: permission denied for id (1220706430)
% 0.98/0.63  % (4546)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.98/0.64  % (4539)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.98/0.64  % (4546)Refutation not found, incomplete strategy% (4546)------------------------------
% 0.98/0.64  % (4546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.98/0.64  % (4546)Termination reason: Refutation not found, incomplete strategy
% 0.98/0.64  
% 0.98/0.64  % (4546)Memory used [KB]: 1663
% 0.98/0.64  % (4546)Time elapsed: 0.056 s
% 0.98/0.64  % (4546)------------------------------
% 0.98/0.64  % (4546)------------------------------
% 0.98/0.64  % (4557)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.98/0.64  % (4539)Refutation not found, incomplete strategy% (4539)------------------------------
% 0.98/0.64  % (4539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.98/0.64  % (4539)Termination reason: Refutation not found, incomplete strategy
% 0.98/0.64  
% 0.98/0.64  % (4539)Memory used [KB]: 10618
% 0.98/0.64  % (4539)Time elapsed: 0.056 s
% 0.98/0.64  % (4539)------------------------------
% 0.98/0.64  % (4539)------------------------------
% 0.98/0.65  % (4541)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.98/0.65  % (4548)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.98/0.65  % (4557)Refutation found. Thanks to Tanya!
% 0.98/0.65  % SZS status Theorem for theBenchmark
% 0.98/0.65  % (4544)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.27/0.66  % (4561)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.27/0.66  % SZS output start Proof for theBenchmark
% 1.27/0.66  fof(f470,plain,(
% 1.27/0.66    $false),
% 1.27/0.66    inference(resolution,[],[f451,f63])).
% 1.27/0.66  fof(f63,plain,(
% 1.27/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.27/0.66    inference(equality_resolution,[],[f59])).
% 1.27/0.66  fof(f59,plain,(
% 1.27/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.27/0.66    inference(cnf_transformation,[],[f36])).
% 1.27/0.66  fof(f36,plain,(
% 1.27/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.27/0.66    inference(flattening,[],[f35])).
% 1.27/0.66  fof(f35,plain,(
% 1.27/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.27/0.66    inference(nnf_transformation,[],[f2])).
% 1.27/0.66  fof(f2,axiom,(
% 1.27/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.27/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.27/0.66  fof(f451,plain,(
% 1.27/0.66    ( ! [X0] : (~r1_tarski(k1_tarski(X0),k1_tarski(sK3(sK1)))) )),
% 1.27/0.66    inference(resolution,[],[f440,f61])).
% 1.27/0.66  fof(f61,plain,(
% 1.27/0.66    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.27/0.66    inference(cnf_transformation,[],[f37])).
% 1.27/0.66  fof(f37,plain,(
% 1.27/0.66    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.27/0.66    inference(nnf_transformation,[],[f3])).
% 1.27/0.66  fof(f3,axiom,(
% 1.27/0.66    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.27/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.27/0.66  fof(f440,plain,(
% 1.27/0.66    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK3(sK1)))) )),
% 1.27/0.66    inference(resolution,[],[f439,f56])).
% 1.27/0.66  fof(f56,plain,(
% 1.27/0.66    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.27/0.66    inference(cnf_transformation,[],[f34])).
% 1.27/0.66  fof(f34,plain,(
% 1.27/0.66    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.27/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 1.27/0.66  fof(f33,plain,(
% 1.27/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.27/0.66    introduced(choice_axiom,[])).
% 1.27/0.66  fof(f32,plain,(
% 1.27/0.66    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.27/0.66    inference(rectify,[],[f31])).
% 1.27/0.66  fof(f31,plain,(
% 1.27/0.66    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.27/0.66    inference(nnf_transformation,[],[f1])).
% 1.27/0.66  fof(f1,axiom,(
% 1.27/0.66    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.27/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.27/0.66  fof(f439,plain,(
% 1.27/0.66    v1_xboole_0(k1_tarski(sK3(sK1)))),
% 1.27/0.66    inference(subsumption_resolution,[],[f437,f244])).
% 1.27/0.66  fof(f244,plain,(
% 1.27/0.66    r1_tarski(sK1,sK2(sK0,sK1))),
% 1.27/0.66    inference(subsumption_resolution,[],[f243,f175])).
% 1.27/0.66  fof(f175,plain,(
% 1.27/0.66    v2_tex_2(sK1,sK0)),
% 1.27/0.66    inference(subsumption_resolution,[],[f133,f129])).
% 1.27/0.66  fof(f129,plain,(
% 1.27/0.66    v2_tex_2(sK1,sK0) | ~v1_zfmisc_1(sK1)),
% 1.27/0.66    inference(subsumption_resolution,[],[f128,f38])).
% 1.27/0.66  fof(f38,plain,(
% 1.27/0.66    ~v2_struct_0(sK0)),
% 1.27/0.66    inference(cnf_transformation,[],[f24])).
% 1.27/0.66  fof(f24,plain,(
% 1.27/0.66    ((~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.27/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).
% 1.27/0.66  fof(f22,plain,(
% 1.27/0.66    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.27/0.66    introduced(choice_axiom,[])).
% 1.27/0.66  fof(f23,plain,(
% 1.27/0.66    ? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 1.27/0.66    introduced(choice_axiom,[])).
% 1.27/0.66  fof(f21,plain,(
% 1.27/0.66    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.27/0.66    inference(flattening,[],[f20])).
% 1.27/0.66  fof(f20,plain,(
% 1.27/0.66    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.27/0.66    inference(nnf_transformation,[],[f11])).
% 1.27/0.66  fof(f11,plain,(
% 1.27/0.66    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.27/0.66    inference(flattening,[],[f10])).
% 1.27/0.66  fof(f10,plain,(
% 1.27/0.66    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.27/0.66    inference(ennf_transformation,[],[f9])).
% 1.27/0.66  fof(f9,negated_conjecture,(
% 1.27/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.27/0.66    inference(negated_conjecture,[],[f8])).
% 1.27/0.66  fof(f8,conjecture,(
% 1.27/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.27/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).
% 1.27/0.66  fof(f128,plain,(
% 1.27/0.66    v2_tex_2(sK1,sK0) | ~v1_zfmisc_1(sK1) | v2_struct_0(sK0)),
% 1.27/0.66    inference(subsumption_resolution,[],[f127,f39])).
% 1.27/0.66  fof(f39,plain,(
% 1.27/0.66    v2_pre_topc(sK0)),
% 1.27/0.66    inference(cnf_transformation,[],[f24])).
% 1.27/0.66  fof(f127,plain,(
% 1.27/0.66    v2_tex_2(sK1,sK0) | ~v1_zfmisc_1(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.27/0.66    inference(subsumption_resolution,[],[f126,f40])).
% 1.27/0.66  fof(f40,plain,(
% 1.27/0.66    v2_tdlat_3(sK0)),
% 1.27/0.66    inference(cnf_transformation,[],[f24])).
% 1.27/0.66  fof(f126,plain,(
% 1.27/0.66    v2_tex_2(sK1,sK0) | ~v1_zfmisc_1(sK1) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.27/0.66    inference(subsumption_resolution,[],[f125,f41])).
% 1.27/0.66  fof(f41,plain,(
% 1.27/0.66    l1_pre_topc(sK0)),
% 1.27/0.66    inference(cnf_transformation,[],[f24])).
% 1.27/0.66  fof(f125,plain,(
% 1.27/0.66    v2_tex_2(sK1,sK0) | ~v1_zfmisc_1(sK1) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.27/0.66    inference(subsumption_resolution,[],[f112,f42])).
% 1.27/0.66  fof(f42,plain,(
% 1.27/0.66    ~v1_xboole_0(sK1)),
% 1.27/0.66    inference(cnf_transformation,[],[f24])).
% 1.27/0.66  fof(f112,plain,(
% 1.27/0.66    v2_tex_2(sK1,sK0) | ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.27/0.66    inference(resolution,[],[f43,f55])).
% 1.27/0.66  fof(f55,plain,(
% 1.27/0.66    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.27/0.66    inference(cnf_transformation,[],[f30])).
% 1.27/0.66  fof(f30,plain,(
% 1.27/0.66    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.27/0.66    inference(nnf_transformation,[],[f19])).
% 1.27/0.66  fof(f19,plain,(
% 1.27/0.66    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.27/0.66    inference(flattening,[],[f18])).
% 1.27/0.66  fof(f18,plain,(
% 1.27/0.66    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.27/0.66    inference(ennf_transformation,[],[f7])).
% 1.27/0.66  fof(f7,axiom,(
% 1.27/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.27/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 1.27/0.66  fof(f43,plain,(
% 1.27/0.66    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.27/0.66    inference(cnf_transformation,[],[f24])).
% 1.27/0.66  fof(f133,plain,(
% 1.27/0.66    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 1.27/0.66    inference(subsumption_resolution,[],[f132,f41])).
% 1.27/0.66  fof(f132,plain,(
% 1.27/0.66    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.27/0.66    inference(subsumption_resolution,[],[f130,f43])).
% 1.27/0.66  fof(f130,plain,(
% 1.27/0.66    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.27/0.66    inference(resolution,[],[f44,f48])).
% 1.27/0.66  fof(f48,plain,(
% 1.27/0.66    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.27/0.66    inference(cnf_transformation,[],[f29])).
% 1.27/0.66  fof(f29,plain,(
% 1.27/0.66    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.27/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 1.27/0.66  fof(f28,plain,(
% 1.27/0.66    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.27/0.66    introduced(choice_axiom,[])).
% 1.27/0.66  fof(f27,plain,(
% 1.27/0.66    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.27/0.66    inference(rectify,[],[f26])).
% 1.27/0.66  fof(f26,plain,(
% 1.27/0.66    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.27/0.66    inference(flattening,[],[f25])).
% 1.27/0.66  fof(f25,plain,(
% 1.27/0.66    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.27/0.66    inference(nnf_transformation,[],[f17])).
% 1.27/0.66  fof(f17,plain,(
% 1.27/0.66    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.27/0.66    inference(flattening,[],[f16])).
% 1.27/0.66  fof(f16,plain,(
% 1.27/0.66    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.27/0.66    inference(ennf_transformation,[],[f5])).
% 1.27/0.66  fof(f5,axiom,(
% 1.27/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.27/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 1.27/0.66  fof(f44,plain,(
% 1.27/0.66    v3_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 1.27/0.66    inference(cnf_transformation,[],[f24])).
% 1.27/0.66  fof(f243,plain,(
% 1.27/0.66    r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 1.27/0.66    inference(subsumption_resolution,[],[f146,f176])).
% 1.27/0.66  fof(f176,plain,(
% 1.27/0.66    v1_zfmisc_1(sK1)),
% 1.27/0.66    inference(resolution,[],[f175,f124])).
% 1.27/0.66  fof(f124,plain,(
% 1.27/0.66    ~v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 1.27/0.66    inference(subsumption_resolution,[],[f123,f38])).
% 1.27/0.66  fof(f123,plain,(
% 1.27/0.66    v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 1.27/0.66    inference(subsumption_resolution,[],[f122,f39])).
% 1.27/0.66  fof(f122,plain,(
% 1.27/0.66    v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.27/0.66    inference(subsumption_resolution,[],[f121,f40])).
% 1.27/0.66  fof(f121,plain,(
% 1.27/0.66    v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.27/0.66    inference(subsumption_resolution,[],[f120,f41])).
% 1.27/0.66  fof(f120,plain,(
% 1.27/0.66    v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.27/0.66    inference(subsumption_resolution,[],[f111,f42])).
% 1.27/0.66  fof(f111,plain,(
% 1.27/0.66    v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.27/0.66    inference(resolution,[],[f43,f54])).
% 1.27/0.66  fof(f54,plain,(
% 1.27/0.66    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.27/0.66    inference(cnf_transformation,[],[f30])).
% 1.27/0.66  fof(f146,plain,(
% 1.27/0.66    ~v1_zfmisc_1(sK1) | r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 1.27/0.66    inference(subsumption_resolution,[],[f145,f41])).
% 1.27/0.66  fof(f145,plain,(
% 1.27/0.66    ~v1_zfmisc_1(sK1) | r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.27/0.66    inference(subsumption_resolution,[],[f139,f43])).
% 1.27/0.66  fof(f139,plain,(
% 1.27/0.66    ~v1_zfmisc_1(sK1) | r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.27/0.66    inference(resolution,[],[f45,f52])).
% 1.27/0.66  fof(f52,plain,(
% 1.27/0.66    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.27/0.66    inference(cnf_transformation,[],[f29])).
% 1.27/0.66  fof(f45,plain,(
% 1.27/0.66    ~v3_tex_2(sK1,sK0) | ~v1_zfmisc_1(sK1)),
% 1.27/0.66    inference(cnf_transformation,[],[f24])).
% 1.27/0.66  fof(f437,plain,(
% 1.27/0.66    ~r1_tarski(sK1,sK2(sK0,sK1)) | v1_xboole_0(k1_tarski(sK3(sK1)))),
% 1.27/0.66    inference(superposition,[],[f394,f255])).
% 1.27/0.66  fof(f255,plain,(
% 1.27/0.66    sK1 = k1_tarski(sK3(sK1)) | v1_xboole_0(k1_tarski(sK3(sK1)))),
% 1.27/0.66    inference(resolution,[],[f102,f208])).
% 1.27/0.66  fof(f208,plain,(
% 1.27/0.66    ( ! [X3] : (~r1_tarski(X3,sK1) | sK1 = X3 | v1_xboole_0(X3)) )),
% 1.27/0.66    inference(subsumption_resolution,[],[f99,f176])).
% 1.27/0.67  % (4554)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.27/0.67  fof(f99,plain,(
% 1.27/0.67    ( ! [X3] : (sK1 = X3 | ~r1_tarski(X3,sK1) | ~v1_zfmisc_1(sK1) | v1_xboole_0(X3)) )),
% 1.27/0.67    inference(resolution,[],[f42,f46])).
% 1.27/0.67  fof(f46,plain,(
% 1.27/0.67    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.27/0.67    inference(cnf_transformation,[],[f13])).
% 1.27/0.67  fof(f13,plain,(
% 1.27/0.67    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.27/0.67    inference(flattening,[],[f12])).
% 1.27/0.67  fof(f12,plain,(
% 1.27/0.67    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.27/0.67    inference(ennf_transformation,[],[f6])).
% 1.27/0.67  fof(f6,axiom,(
% 1.27/0.67    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.27/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 1.27/0.67  fof(f102,plain,(
% 1.27/0.67    r1_tarski(k1_tarski(sK3(sK1)),sK1)),
% 1.27/0.67    inference(resolution,[],[f95,f62])).
% 1.27/0.67  fof(f62,plain,(
% 1.27/0.67    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.27/0.67    inference(cnf_transformation,[],[f37])).
% 1.27/0.67  fof(f95,plain,(
% 1.27/0.67    r2_hidden(sK3(sK1),sK1)),
% 1.27/0.67    inference(resolution,[],[f42,f57])).
% 1.27/0.67  fof(f57,plain,(
% 1.27/0.67    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.27/0.67    inference(cnf_transformation,[],[f34])).
% 1.27/0.67  fof(f394,plain,(
% 1.27/0.67    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK2(sK0,sK1))) )),
% 1.27/0.67    inference(resolution,[],[f392,f61])).
% 1.27/0.67  fof(f392,plain,(
% 1.27/0.67    ( ! [X0] : (~r2_hidden(X0,sK2(sK0,sK1))) )),
% 1.27/0.67    inference(resolution,[],[f391,f56])).
% 1.27/0.67  fof(f391,plain,(
% 1.27/0.67    v1_xboole_0(sK2(sK0,sK1))),
% 1.27/0.67    inference(subsumption_resolution,[],[f390,f282])).
% 1.27/0.67  fof(f282,plain,(
% 1.27/0.67    v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1))),
% 1.27/0.67    inference(subsumption_resolution,[],[f271,f213])).
% 1.27/0.67  fof(f213,plain,(
% 1.27/0.67    v2_tex_2(sK2(sK0,sK1),sK0)),
% 1.27/0.67    inference(subsumption_resolution,[],[f212,f175])).
% 1.27/0.67  fof(f212,plain,(
% 1.27/0.67    v2_tex_2(sK2(sK0,sK1),sK0) | ~v2_tex_2(sK1,sK0)),
% 1.27/0.67    inference(subsumption_resolution,[],[f144,f176])).
% 1.27/0.67  fof(f144,plain,(
% 1.27/0.67    ~v1_zfmisc_1(sK1) | v2_tex_2(sK2(sK0,sK1),sK0) | ~v2_tex_2(sK1,sK0)),
% 1.27/0.67    inference(subsumption_resolution,[],[f143,f41])).
% 1.27/0.67  fof(f143,plain,(
% 1.27/0.67    ~v1_zfmisc_1(sK1) | v2_tex_2(sK2(sK0,sK1),sK0) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.27/0.67    inference(subsumption_resolution,[],[f138,f43])).
% 1.27/0.67  fof(f138,plain,(
% 1.27/0.67    ~v1_zfmisc_1(sK1) | v2_tex_2(sK2(sK0,sK1),sK0) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.27/0.67    inference(resolution,[],[f45,f51])).
% 1.27/0.67  fof(f51,plain,(
% 1.27/0.67    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.27/0.67    inference(cnf_transformation,[],[f29])).
% 1.27/0.67  fof(f271,plain,(
% 1.27/0.67    ~v2_tex_2(sK2(sK0,sK1),sK0) | v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1))),
% 1.27/0.67    inference(resolution,[],[f269,f91])).
% 1.27/0.67  fof(f91,plain,(
% 1.27/0.67    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X7,sK0) | v1_zfmisc_1(X7) | v1_xboole_0(X7)) )),
% 1.27/0.67    inference(subsumption_resolution,[],[f90,f38])).
% 1.27/0.67  fof(f90,plain,(
% 1.27/0.67    ( ! [X7] : (v1_zfmisc_1(X7) | ~v2_tex_2(X7,sK0) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X7) | v2_struct_0(sK0)) )),
% 1.27/0.67    inference(subsumption_resolution,[],[f89,f39])).
% 1.27/0.67  fof(f89,plain,(
% 1.27/0.67    ( ! [X7] : (v1_zfmisc_1(X7) | ~v2_tex_2(X7,sK0) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X7) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.27/0.67    inference(subsumption_resolution,[],[f87,f40])).
% 1.27/0.67  fof(f87,plain,(
% 1.27/0.67    ( ! [X7] : (v1_zfmisc_1(X7) | ~v2_tex_2(X7,sK0) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X7) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.27/0.67    inference(resolution,[],[f41,f54])).
% 1.27/0.67  fof(f269,plain,(
% 1.27/0.67    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.27/0.67    inference(subsumption_resolution,[],[f268,f175])).
% 1.27/0.67  fof(f268,plain,(
% 1.27/0.67    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0)),
% 1.27/0.67    inference(subsumption_resolution,[],[f142,f176])).
% 1.27/0.67  fof(f142,plain,(
% 1.27/0.67    ~v1_zfmisc_1(sK1) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0)),
% 1.27/0.67    inference(subsumption_resolution,[],[f141,f41])).
% 1.27/0.67  fof(f141,plain,(
% 1.27/0.67    ~v1_zfmisc_1(sK1) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.27/0.67    inference(subsumption_resolution,[],[f137,f43])).
% 1.27/0.67  fof(f137,plain,(
% 1.27/0.67    ~v1_zfmisc_1(sK1) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.27/0.67    inference(resolution,[],[f45,f50])).
% 1.27/0.67  fof(f50,plain,(
% 1.27/0.67    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.27/0.67    inference(cnf_transformation,[],[f29])).
% 1.27/0.67  fof(f390,plain,(
% 1.27/0.67    ~v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1))),
% 1.27/0.67    inference(subsumption_resolution,[],[f249,f252])).
% 1.27/0.67  fof(f252,plain,(
% 1.27/0.67    sK1 != sK2(sK0,sK1)),
% 1.27/0.67    inference(subsumption_resolution,[],[f251,f175])).
% 1.27/0.67  fof(f251,plain,(
% 1.27/0.67    sK1 != sK2(sK0,sK1) | ~v2_tex_2(sK1,sK0)),
% 1.27/0.67    inference(subsumption_resolution,[],[f148,f176])).
% 1.27/0.67  fof(f148,plain,(
% 1.27/0.67    ~v1_zfmisc_1(sK1) | sK1 != sK2(sK0,sK1) | ~v2_tex_2(sK1,sK0)),
% 1.27/0.67    inference(subsumption_resolution,[],[f147,f41])).
% 1.27/0.67  fof(f147,plain,(
% 1.27/0.67    ~v1_zfmisc_1(sK1) | sK1 != sK2(sK0,sK1) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.27/0.67    inference(subsumption_resolution,[],[f140,f43])).
% 1.27/0.67  fof(f140,plain,(
% 1.27/0.67    ~v1_zfmisc_1(sK1) | sK1 != sK2(sK0,sK1) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.27/0.67    inference(resolution,[],[f45,f53])).
% 1.27/0.67  fof(f53,plain,(
% 1.27/0.67    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK2(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.27/0.67    inference(cnf_transformation,[],[f29])).
% 1.27/0.67  fof(f249,plain,(
% 1.27/0.67    sK1 = sK2(sK0,sK1) | ~v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1))),
% 1.27/0.67    inference(resolution,[],[f244,f98])).
% 1.27/0.67  fof(f98,plain,(
% 1.27/0.67    ( ! [X2] : (~r1_tarski(sK1,X2) | sK1 = X2 | ~v1_zfmisc_1(X2) | v1_xboole_0(X2)) )),
% 1.27/0.67    inference(resolution,[],[f42,f46])).
% 1.27/0.67  % SZS output end Proof for theBenchmark
% 1.27/0.67  % (4557)------------------------------
% 1.27/0.67  % (4557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.67  % (4557)Termination reason: Refutation
% 1.27/0.67  
% 1.27/0.67  % (4557)Memory used [KB]: 1791
% 1.27/0.67  % (4557)Time elapsed: 0.069 s
% 1.27/0.67  % (4557)------------------------------
% 1.27/0.67  % (4557)------------------------------
% 1.27/0.67  % (4405)Success in time 0.306 s
%------------------------------------------------------------------------------
