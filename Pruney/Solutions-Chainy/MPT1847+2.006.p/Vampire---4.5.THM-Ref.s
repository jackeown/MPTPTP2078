%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:34 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  151 (1755 expanded)
%              Number of leaves         :   19 ( 606 expanded)
%              Depth                    :   27
%              Number of atoms          :  449 (9833 expanded)
%              Number of equality atoms :   77 (1747 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1043,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f510,f1036])).

fof(f1036,plain,(
    ~ spl4_37 ),
    inference(avatar_contradiction_clause,[],[f1035])).

fof(f1035,plain,
    ( $false
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f992,f230])).

fof(f230,plain,(
    ! [X2] : ~ v1_subset_1(X2,X2) ),
    inference(resolution,[],[f88,f78])).

fof(f78,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f88,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f74,f79])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f992,plain,
    ( v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl4_37 ),
    inference(superposition,[],[f104,f987])).

fof(f987,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f986,f982])).

fof(f982,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f981,f700])).

fof(f700,plain,(
    u1_struct_0(sK0) = u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f699,f474])).

fof(f474,plain,(
    u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f473,f88])).

fof(f473,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f472,f177])).

fof(f177,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f163,f176])).

fof(f176,plain,(
    ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f175,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ v1_tex_2(sK2,sK0)
    & v1_tex_2(sK1,sK0)
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & m1_pre_topc(sK2,sK0)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tex_2(X2,X0)
                & v1_tex_2(X1,X0)
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,sK0)
              & v1_tex_2(X1,sK0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,sK0) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tex_2(X2,sK0)
            & v1_tex_2(X1,sK0)
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
            & m1_pre_topc(X2,sK0) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ~ v1_tex_2(X2,sK0)
          & v1_tex_2(sK1,sK0)
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & m1_pre_topc(X2,sK0) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ~ v1_tex_2(X2,sK0)
        & v1_tex_2(sK1,sK0)
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_pre_topc(X2,sK0) )
   => ( ~ v1_tex_2(sK2,sK0)
      & v1_tex_2(sK1,sK0)
      & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( ( v1_tex_2(X1,X0)
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
               => v1_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).

fof(f175,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f174,f48])).

fof(f48,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f174,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f168,f51])).

fof(f51,plain,(
    ~ v1_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f168,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | v1_tex_2(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f62,f116])).

fof(f116,plain,(
    u1_struct_0(sK2) = sK3(sK0,sK2) ),
    inference(subsumption_resolution,[],[f115,f46])).

fof(f115,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f114,f51])).

fof(f114,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | v1_tex_2(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f61,f48])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | v1_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f163,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK0)
    | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f98,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f98,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f96,f46])).

fof(f96,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f58,f48])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f472,plain,
    ( u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f471,f87])).

fof(f87,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f85,f46])).

fof(f85,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f56,f48])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f471,plain,
    ( u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f464,f376])).

fof(f376,plain,(
    v1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f375,f177])).

fof(f375,plain,(
    v1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2))) ),
    inference(resolution,[],[f232,f87])).

fof(f232,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(X4)
      | v1_pre_topc(k1_pre_topc(X4,u1_struct_0(X4))) ) ),
    inference(resolution,[],[f88,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f464,plain,
    ( u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0)))
    | ~ v1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f380,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f380,plain,(
    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),sK2) ),
    inference(forward_demodulation,[],[f379,f177])).

fof(f379,plain,(
    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2)),sK2) ),
    inference(resolution,[],[f231,f87])).

fof(f231,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(X3)
      | m1_pre_topc(k1_pre_topc(X3,u1_struct_0(X3)),X3) ) ),
    inference(resolution,[],[f88,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f699,plain,(
    k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) = u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(resolution,[],[f572,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f572,plain,(
    l1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(resolution,[],[f508,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f508,plain,(
    l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f470,f87])).

fof(f470,plain,
    ( l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f380,f56])).

fof(f981,plain,
    ( r1_tarski(u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))),u1_struct_0(sK1))
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f957,f86])).

fof(f86,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f84,f46])).

fof(f84,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f56,f47])).

fof(f47,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f957,plain,
    ( r1_tarski(u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ spl4_37 ),
    inference(resolution,[],[f788,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f788,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),sK1)
    | ~ spl4_37 ),
    inference(resolution,[],[f593,f502])).

fof(f502,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f500])).

fof(f500,plain,
    ( spl4_37
  <=> m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f593,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)))
      | m1_pre_topc(X2,sK1) ) ),
    inference(subsumption_resolution,[],[f591,f86])).

fof(f591,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)))
      | m1_pre_topc(X2,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f65,f233])).

fof(f233,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)) ),
    inference(superposition,[],[f49,f177])).

fof(f49,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f986,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f525,f399])).

fof(f399,plain,(
    u1_struct_0(sK1) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f398,f263])).

fof(f263,plain,(
    u1_struct_0(sK1) = k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f262,f46])).

fof(f262,plain,
    ( u1_struct_0(sK1) = k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f261,f97])).

fof(f97,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f95,f46])).

fof(f95,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f58,f47])).

fof(f261,plain,
    ( u1_struct_0(sK1) = k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f254,f150])).

fof(f150,plain,(
    v1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f146,f46])).

fof(f146,plain,
    ( v1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f97,f68])).

fof(f254,plain,
    ( u1_struct_0(sK1) = k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))
    | ~ v1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f149,f77])).

fof(f149,plain,(
    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f145,f46])).

fof(f145,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f97,f69])).

fof(f398,plain,(
    k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) ),
    inference(resolution,[],[f394,f52])).

fof(f394,plain,(
    l1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) ),
    inference(resolution,[],[f292,f53])).

fof(f292,plain,(
    l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f260,f46])).

fof(f260,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f149,f56])).

fof(f525,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f523,f399])).

fof(f523,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))) ),
    inference(resolution,[],[f291,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f291,plain,(
    r1_tarski(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f259,f46])).

fof(f259,plain,
    ( r1_tarski(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f149,f57])).

fof(f104,plain,(
    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f103,f46])).

fof(f103,plain,
    ( v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f102,f47])).

fof(f102,plain,
    ( v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f81,f50])).

fof(f50,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f75,f58])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f510,plain,(
    spl4_37 ),
    inference(avatar_contradiction_clause,[],[f509])).

fof(f509,plain,
    ( $false
    | spl4_37 ),
    inference(global_subsumption,[],[f494,f508,f501])).

fof(f501,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)))
    | spl4_37 ),
    inference(avatar_component_clause,[],[f500])).

fof(f494,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f493,f233])).

fof(f493,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f492,f49])).

fof(f492,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f467,f87])).

fof(f467,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(resolution,[],[f380,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:15:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.51  % (12382)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (12392)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (12383)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (12398)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (12385)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (12391)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (12385)Refutation not found, incomplete strategy% (12385)------------------------------
% 0.22/0.52  % (12385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12385)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12385)Memory used [KB]: 6140
% 0.22/0.52  % (12385)Time elapsed: 0.092 s
% 0.22/0.52  % (12385)------------------------------
% 0.22/0.52  % (12385)------------------------------
% 0.22/0.52  % (12393)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (12396)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (12394)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (12402)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (12401)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (12400)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.53  % (12387)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (12389)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (12388)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (12381)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (12384)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.54  % (12403)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (12393)Refutation not found, incomplete strategy% (12393)------------------------------
% 0.22/0.54  % (12393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12393)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12393)Memory used [KB]: 6396
% 0.22/0.54  % (12393)Time elapsed: 0.115 s
% 0.22/0.54  % (12393)------------------------------
% 0.22/0.54  % (12393)------------------------------
% 0.22/0.55  % (12386)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.55  % (12380)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.55  % (12380)Refutation not found, incomplete strategy% (12380)------------------------------
% 0.22/0.55  % (12380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (12380)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (12380)Memory used [KB]: 10618
% 0.22/0.55  % (12380)Time elapsed: 0.126 s
% 0.22/0.55  % (12380)------------------------------
% 0.22/0.55  % (12380)------------------------------
% 1.43/0.55  % (12404)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.43/0.56  % (12390)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.43/0.56  % (12399)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.43/0.57  % (12405)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.43/0.57  % (12397)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.43/0.57  % (12386)Refutation not found, incomplete strategy% (12386)------------------------------
% 1.43/0.57  % (12386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (12386)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.57  
% 1.43/0.57  % (12386)Memory used [KB]: 10618
% 1.43/0.57  % (12386)Time elapsed: 0.120 s
% 1.43/0.57  % (12386)------------------------------
% 1.43/0.57  % (12386)------------------------------
% 1.61/0.58  % (12406)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.61/0.61  % (12390)Refutation found. Thanks to Tanya!
% 1.61/0.61  % SZS status Theorem for theBenchmark
% 1.61/0.61  % SZS output start Proof for theBenchmark
% 1.61/0.61  fof(f1043,plain,(
% 1.61/0.61    $false),
% 1.61/0.61    inference(avatar_sat_refutation,[],[f510,f1036])).
% 1.61/0.61  fof(f1036,plain,(
% 1.61/0.61    ~spl4_37),
% 1.61/0.61    inference(avatar_contradiction_clause,[],[f1035])).
% 1.61/0.61  fof(f1035,plain,(
% 1.61/0.61    $false | ~spl4_37),
% 1.61/0.61    inference(subsumption_resolution,[],[f992,f230])).
% 1.61/0.61  fof(f230,plain,(
% 1.61/0.61    ( ! [X2] : (~v1_subset_1(X2,X2)) )),
% 1.61/0.61    inference(resolution,[],[f88,f78])).
% 1.61/0.61  fof(f78,plain,(
% 1.61/0.61    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 1.61/0.61    inference(equality_resolution,[],[f66])).
% 1.61/0.61  fof(f66,plain,(
% 1.61/0.61    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.61    inference(cnf_transformation,[],[f42])).
% 1.61/0.61  fof(f42,plain,(
% 1.61/0.61    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.61    inference(nnf_transformation,[],[f29])).
% 1.61/0.61  fof(f29,plain,(
% 1.61/0.61    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.61    inference(ennf_transformation,[],[f13])).
% 1.61/0.61  fof(f13,axiom,(
% 1.61/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 1.61/0.61  fof(f88,plain,(
% 1.61/0.61    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.61/0.61    inference(resolution,[],[f74,f79])).
% 1.61/0.61  fof(f79,plain,(
% 1.61/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.61/0.61    inference(equality_resolution,[],[f71])).
% 1.61/0.61  fof(f71,plain,(
% 1.61/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.61/0.61    inference(cnf_transformation,[],[f44])).
% 1.61/0.61  fof(f44,plain,(
% 1.61/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.61/0.61    inference(flattening,[],[f43])).
% 1.61/0.61  fof(f43,plain,(
% 1.61/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.61/0.61    inference(nnf_transformation,[],[f1])).
% 1.61/0.61  fof(f1,axiom,(
% 1.61/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.61/0.61  fof(f74,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.61/0.61    inference(cnf_transformation,[],[f45])).
% 1.61/0.61  fof(f45,plain,(
% 1.61/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.61/0.61    inference(nnf_transformation,[],[f2])).
% 1.61/0.61  fof(f2,axiom,(
% 1.61/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.61/0.61  fof(f992,plain,(
% 1.61/0.61    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl4_37),
% 1.61/0.61    inference(superposition,[],[f104,f987])).
% 1.61/0.61  fof(f987,plain,(
% 1.61/0.61    u1_struct_0(sK1) = u1_struct_0(sK0) | ~spl4_37),
% 1.61/0.61    inference(subsumption_resolution,[],[f986,f982])).
% 1.61/0.61  fof(f982,plain,(
% 1.61/0.61    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl4_37),
% 1.61/0.61    inference(forward_demodulation,[],[f981,f700])).
% 1.61/0.61  fof(f700,plain,(
% 1.61/0.61    u1_struct_0(sK0) = u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 1.61/0.61    inference(forward_demodulation,[],[f699,f474])).
% 1.61/0.61  fof(f474,plain,(
% 1.61/0.61    u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 1.61/0.61    inference(subsumption_resolution,[],[f473,f88])).
% 1.61/0.61  fof(f473,plain,(
% 1.61/0.61    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 1.61/0.61    inference(forward_demodulation,[],[f472,f177])).
% 1.61/0.61  fof(f177,plain,(
% 1.61/0.61    u1_struct_0(sK2) = u1_struct_0(sK0)),
% 1.61/0.61    inference(subsumption_resolution,[],[f163,f176])).
% 1.61/0.61  fof(f176,plain,(
% 1.61/0.61    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))),
% 1.61/0.61    inference(subsumption_resolution,[],[f175,f46])).
% 1.61/0.61  fof(f46,plain,(
% 1.61/0.61    l1_pre_topc(sK0)),
% 1.61/0.61    inference(cnf_transformation,[],[f35])).
% 1.61/0.61  fof(f35,plain,(
% 1.61/0.61    ((~v1_tex_2(sK2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(sK2,sK0)) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 1.61/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f34,f33,f32])).
% 1.61/0.61  fof(f32,plain,(
% 1.61/0.61    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(X1,sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 1.61/0.61    introduced(choice_axiom,[])).
% 1.61/0.61  fof(f33,plain,(
% 1.61/0.61    ? [X1] : (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(X1,sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) => (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(sK1,sK0))),
% 1.61/0.61    introduced(choice_axiom,[])).
% 1.61/0.61  fof(f34,plain,(
% 1.61/0.61    ? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(X2,sK0)) => (~v1_tex_2(sK2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(sK2,sK0))),
% 1.61/0.61    introduced(choice_axiom,[])).
% 1.61/0.61  fof(f17,plain,(
% 1.61/0.61    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 1.61/0.61    inference(flattening,[],[f16])).
% 1.61/0.61  fof(f16,plain,(
% 1.61/0.61    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X2,X0) & (v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 1.61/0.61    inference(ennf_transformation,[],[f15])).
% 1.61/0.61  fof(f15,negated_conjecture,(
% 1.61/0.61    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 1.61/0.61    inference(negated_conjecture,[],[f14])).
% 1.61/0.61  fof(f14,conjecture,(
% 1.61/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).
% 1.61/0.61  fof(f175,plain,(
% 1.61/0.61    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 1.61/0.61    inference(subsumption_resolution,[],[f174,f48])).
% 1.61/0.61  fof(f48,plain,(
% 1.61/0.61    m1_pre_topc(sK2,sK0)),
% 1.61/0.61    inference(cnf_transformation,[],[f35])).
% 1.61/0.61  fof(f174,plain,(
% 1.61/0.61    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0)),
% 1.61/0.61    inference(subsumption_resolution,[],[f168,f51])).
% 1.61/0.61  fof(f51,plain,(
% 1.61/0.61    ~v1_tex_2(sK2,sK0)),
% 1.61/0.61    inference(cnf_transformation,[],[f35])).
% 1.61/0.61  fof(f168,plain,(
% 1.61/0.61    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | v1_tex_2(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0)),
% 1.61/0.61    inference(superposition,[],[f62,f116])).
% 1.61/0.61  fof(f116,plain,(
% 1.61/0.61    u1_struct_0(sK2) = sK3(sK0,sK2)),
% 1.61/0.61    inference(subsumption_resolution,[],[f115,f46])).
% 1.61/0.61  fof(f115,plain,(
% 1.61/0.61    u1_struct_0(sK2) = sK3(sK0,sK2) | ~l1_pre_topc(sK0)),
% 1.61/0.61    inference(subsumption_resolution,[],[f114,f51])).
% 1.61/0.61  fof(f114,plain,(
% 1.61/0.61    u1_struct_0(sK2) = sK3(sK0,sK2) | v1_tex_2(sK2,sK0) | ~l1_pre_topc(sK0)),
% 1.61/0.61    inference(resolution,[],[f61,f48])).
% 1.61/0.61  fof(f61,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK3(X0,X1) | v1_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f40])).
% 1.61/0.61  fof(f40,plain,(
% 1.61/0.61    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.61/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 1.61/0.61  fof(f39,plain,(
% 1.61/0.61    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.61/0.61    introduced(choice_axiom,[])).
% 1.61/0.61  fof(f38,plain,(
% 1.61/0.61    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.61/0.61    inference(rectify,[],[f37])).
% 1.61/0.61  fof(f37,plain,(
% 1.61/0.61    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.61/0.61    inference(nnf_transformation,[],[f25])).
% 1.61/0.61  fof(f25,plain,(
% 1.61/0.61    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.61/0.61    inference(flattening,[],[f24])).
% 1.61/0.61  fof(f24,plain,(
% 1.61/0.61    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.61/0.61    inference(ennf_transformation,[],[f12])).
% 1.61/0.61  fof(f12,axiom,(
% 1.61/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 1.61/0.61  fof(f62,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f40])).
% 1.61/0.61  fof(f163,plain,(
% 1.61/0.61    u1_struct_0(sK2) = u1_struct_0(sK0) | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))),
% 1.61/0.61    inference(resolution,[],[f98,f67])).
% 1.61/0.61  fof(f67,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f42])).
% 1.61/0.61  fof(f98,plain,(
% 1.61/0.61    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.61/0.61    inference(subsumption_resolution,[],[f96,f46])).
% 1.61/0.61  fof(f96,plain,(
% 1.61/0.61    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.61/0.61    inference(resolution,[],[f58,f48])).
% 1.61/0.61  fof(f58,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f23])).
% 1.61/0.61  fof(f23,plain,(
% 1.61/0.61    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.61/0.61    inference(ennf_transformation,[],[f10])).
% 1.61/0.61  fof(f10,axiom,(
% 1.61/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.61/0.61  fof(f472,plain,(
% 1.61/0.61    u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.61/0.61    inference(subsumption_resolution,[],[f471,f87])).
% 1.61/0.61  fof(f87,plain,(
% 1.61/0.61    l1_pre_topc(sK2)),
% 1.61/0.61    inference(subsumption_resolution,[],[f85,f46])).
% 1.61/0.61  fof(f85,plain,(
% 1.61/0.61    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 1.61/0.61    inference(resolution,[],[f56,f48])).
% 1.61/0.61  fof(f56,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f21])).
% 1.61/0.61  fof(f21,plain,(
% 1.61/0.61    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.61/0.61    inference(ennf_transformation,[],[f7])).
% 1.61/0.61  fof(f7,axiom,(
% 1.61/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.61/0.61  fof(f471,plain,(
% 1.61/0.61    u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 1.61/0.61    inference(subsumption_resolution,[],[f464,f376])).
% 1.61/0.61  fof(f376,plain,(
% 1.61/0.61    v1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 1.61/0.61    inference(forward_demodulation,[],[f375,f177])).
% 1.61/0.61  fof(f375,plain,(
% 1.61/0.61    v1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2)))),
% 1.61/0.61    inference(resolution,[],[f232,f87])).
% 1.61/0.61  fof(f232,plain,(
% 1.61/0.61    ( ! [X4] : (~l1_pre_topc(X4) | v1_pre_topc(k1_pre_topc(X4,u1_struct_0(X4)))) )),
% 1.61/0.61    inference(resolution,[],[f88,f68])).
% 1.61/0.61  fof(f68,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f31])).
% 1.61/0.61  fof(f31,plain,(
% 1.61/0.61    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.61/0.61    inference(flattening,[],[f30])).
% 1.61/0.61  fof(f30,plain,(
% 1.61/0.61    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.61/0.61    inference(ennf_transformation,[],[f5])).
% 1.61/0.61  fof(f5,axiom,(
% 1.61/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 1.61/0.61  fof(f464,plain,(
% 1.61/0.61    u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) | ~v1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 1.61/0.61    inference(resolution,[],[f380,f77])).
% 1.61/0.61  fof(f77,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.61/0.61    inference(equality_resolution,[],[f63])).
% 1.61/0.61  fof(f63,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f41])).
% 1.61/0.61  fof(f41,plain,(
% 1.61/0.61    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.61    inference(nnf_transformation,[],[f27])).
% 1.61/0.61  fof(f27,plain,(
% 1.61/0.61    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.61    inference(flattening,[],[f26])).
% 1.61/0.61  fof(f26,plain,(
% 1.61/0.61    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.61    inference(ennf_transformation,[],[f3])).
% 1.61/0.61  fof(f3,axiom,(
% 1.61/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).
% 1.61/0.61  fof(f380,plain,(
% 1.61/0.61    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),sK2)),
% 1.61/0.61    inference(forward_demodulation,[],[f379,f177])).
% 1.61/0.61  fof(f379,plain,(
% 1.61/0.61    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2)),sK2)),
% 1.61/0.61    inference(resolution,[],[f231,f87])).
% 1.61/0.61  fof(f231,plain,(
% 1.61/0.61    ( ! [X3] : (~l1_pre_topc(X3) | m1_pre_topc(k1_pre_topc(X3,u1_struct_0(X3)),X3)) )),
% 1.61/0.61    inference(resolution,[],[f88,f69])).
% 1.61/0.61  fof(f69,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f31])).
% 1.61/0.61  fof(f699,plain,(
% 1.61/0.61    k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) = u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 1.61/0.61    inference(resolution,[],[f572,f52])).
% 1.61/0.61  fof(f52,plain,(
% 1.61/0.61    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f18])).
% 1.61/0.61  fof(f18,plain,(
% 1.61/0.61    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.61/0.61    inference(ennf_transformation,[],[f4])).
% 1.61/0.61  fof(f4,axiom,(
% 1.61/0.61    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.61/0.61  fof(f572,plain,(
% 1.61/0.61    l1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 1.61/0.61    inference(resolution,[],[f508,f53])).
% 1.61/0.61  fof(f53,plain,(
% 1.61/0.61    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f19])).
% 1.61/0.61  fof(f19,plain,(
% 1.61/0.61    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.61/0.61    inference(ennf_transformation,[],[f6])).
% 1.61/0.61  fof(f6,axiom,(
% 1.61/0.61    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.61/0.61  fof(f508,plain,(
% 1.61/0.61    l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 1.61/0.61    inference(subsumption_resolution,[],[f470,f87])).
% 1.61/0.61  fof(f470,plain,(
% 1.61/0.61    l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0))) | ~l1_pre_topc(sK2)),
% 1.61/0.61    inference(resolution,[],[f380,f56])).
% 1.61/0.61  fof(f981,plain,(
% 1.61/0.61    r1_tarski(u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))),u1_struct_0(sK1)) | ~spl4_37),
% 1.61/0.61    inference(subsumption_resolution,[],[f957,f86])).
% 1.61/0.61  fof(f86,plain,(
% 1.61/0.61    l1_pre_topc(sK1)),
% 1.61/0.61    inference(subsumption_resolution,[],[f84,f46])).
% 1.61/0.61  fof(f84,plain,(
% 1.61/0.61    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 1.61/0.61    inference(resolution,[],[f56,f47])).
% 1.61/0.61  fof(f47,plain,(
% 1.61/0.61    m1_pre_topc(sK1,sK0)),
% 1.61/0.61    inference(cnf_transformation,[],[f35])).
% 1.61/0.61  fof(f957,plain,(
% 1.61/0.61    r1_tarski(u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~spl4_37),
% 1.61/0.61    inference(resolution,[],[f788,f57])).
% 1.61/0.61  fof(f57,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f22])).
% 1.61/0.61  fof(f22,plain,(
% 1.61/0.61    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.61/0.61    inference(ennf_transformation,[],[f11])).
% 1.61/0.61  fof(f11,axiom,(
% 1.61/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 1.61/0.61  fof(f788,plain,(
% 1.61/0.61    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),sK1) | ~spl4_37),
% 1.61/0.61    inference(resolution,[],[f593,f502])).
% 1.61/0.61  fof(f502,plain,(
% 1.61/0.61    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))) | ~spl4_37),
% 1.61/0.61    inference(avatar_component_clause,[],[f500])).
% 1.61/0.61  fof(f500,plain,(
% 1.61/0.61    spl4_37 <=> m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)))),
% 1.61/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.61/0.61  fof(f593,plain,(
% 1.61/0.61    ( ! [X2] : (~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))) | m1_pre_topc(X2,sK1)) )),
% 1.61/0.61    inference(subsumption_resolution,[],[f591,f86])).
% 1.61/0.61  fof(f591,plain,(
% 1.61/0.61    ( ! [X2] : (~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))) | m1_pre_topc(X2,sK1) | ~l1_pre_topc(sK1)) )),
% 1.61/0.61    inference(superposition,[],[f65,f233])).
% 1.61/0.61  fof(f233,plain,(
% 1.61/0.61    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))),
% 1.61/0.61    inference(superposition,[],[f49,f177])).
% 1.61/0.61  fof(f49,plain,(
% 1.61/0.61    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 1.61/0.61    inference(cnf_transformation,[],[f35])).
% 1.61/0.61  fof(f65,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f28])).
% 1.61/0.61  fof(f28,plain,(
% 1.61/0.61    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.61    inference(ennf_transformation,[],[f8])).
% 1.61/0.61  fof(f8,axiom,(
% 1.61/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 1.61/0.61  fof(f986,plain,(
% 1.61/0.61    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | u1_struct_0(sK1) = u1_struct_0(sK0)),
% 1.61/0.61    inference(forward_demodulation,[],[f525,f399])).
% 1.61/0.61  fof(f399,plain,(
% 1.61/0.61    u1_struct_0(sK1) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))),
% 1.61/0.61    inference(forward_demodulation,[],[f398,f263])).
% 1.61/0.61  fof(f263,plain,(
% 1.61/0.61    u1_struct_0(sK1) = k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))),
% 1.61/0.61    inference(subsumption_resolution,[],[f262,f46])).
% 1.61/0.61  fof(f262,plain,(
% 1.61/0.61    u1_struct_0(sK1) = k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0)),
% 1.61/0.61    inference(subsumption_resolution,[],[f261,f97])).
% 1.61/0.61  fof(f97,plain,(
% 1.61/0.61    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.61/0.61    inference(subsumption_resolution,[],[f95,f46])).
% 1.61/0.61  fof(f95,plain,(
% 1.61/0.61    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.61/0.61    inference(resolution,[],[f58,f47])).
% 1.61/0.61  fof(f261,plain,(
% 1.61/0.61    u1_struct_0(sK1) = k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.61/0.61    inference(subsumption_resolution,[],[f254,f150])).
% 1.61/0.61  fof(f150,plain,(
% 1.61/0.61    v1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1)))),
% 1.61/0.61    inference(subsumption_resolution,[],[f146,f46])).
% 1.61/0.61  fof(f146,plain,(
% 1.61/0.61    v1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0)),
% 1.61/0.61    inference(resolution,[],[f97,f68])).
% 1.61/0.61  fof(f254,plain,(
% 1.61/0.61    u1_struct_0(sK1) = k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) | ~v1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.61/0.61    inference(resolution,[],[f149,f77])).
% 1.61/0.61  fof(f149,plain,(
% 1.61/0.61    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1)),sK0)),
% 1.61/0.61    inference(subsumption_resolution,[],[f145,f46])).
% 1.61/0.61  fof(f145,plain,(
% 1.61/0.61    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1)),sK0) | ~l1_pre_topc(sK0)),
% 1.61/0.61    inference(resolution,[],[f97,f69])).
% 1.61/0.61  fof(f398,plain,(
% 1.61/0.61    k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))),
% 1.61/0.61    inference(resolution,[],[f394,f52])).
% 1.61/0.61  fof(f394,plain,(
% 1.61/0.61    l1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))),
% 1.61/0.61    inference(resolution,[],[f292,f53])).
% 1.61/0.61  fof(f292,plain,(
% 1.61/0.61    l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1)))),
% 1.61/0.61    inference(subsumption_resolution,[],[f260,f46])).
% 1.61/0.61  fof(f260,plain,(
% 1.61/0.61    l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0)),
% 1.61/0.61    inference(resolution,[],[f149,f56])).
% 1.61/0.61  fof(f525,plain,(
% 1.61/0.61    u1_struct_0(sK1) = u1_struct_0(sK0) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))))),
% 1.61/0.61    inference(forward_demodulation,[],[f523,f399])).
% 1.61/0.61  fof(f523,plain,(
% 1.61/0.61    u1_struct_0(sK0) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))))),
% 1.61/0.61    inference(resolution,[],[f291,f72])).
% 1.61/0.61  fof(f72,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f44])).
% 1.61/0.61  fof(f291,plain,(
% 1.61/0.61    r1_tarski(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))),u1_struct_0(sK0))),
% 1.61/0.61    inference(subsumption_resolution,[],[f259,f46])).
% 1.61/0.61  fof(f259,plain,(
% 1.61/0.61    r1_tarski(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 1.61/0.61    inference(resolution,[],[f149,f57])).
% 1.61/0.61  fof(f104,plain,(
% 1.61/0.61    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.61/0.61    inference(subsumption_resolution,[],[f103,f46])).
% 1.61/0.61  fof(f103,plain,(
% 1.61/0.61    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 1.61/0.61    inference(subsumption_resolution,[],[f102,f47])).
% 1.61/0.61  fof(f102,plain,(
% 1.61/0.61    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.61/0.61    inference(resolution,[],[f81,f50])).
% 1.61/0.61  fof(f50,plain,(
% 1.61/0.61    v1_tex_2(sK1,sK0)),
% 1.61/0.61    inference(cnf_transformation,[],[f35])).
% 1.61/0.61  fof(f81,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.61/0.61    inference(subsumption_resolution,[],[f75,f58])).
% 1.61/0.61  fof(f75,plain,(
% 1.61/0.61    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.61/0.61    inference(equality_resolution,[],[f59])).
% 1.61/0.61  fof(f59,plain,(
% 1.61/0.61    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f40])).
% 1.61/0.61  fof(f510,plain,(
% 1.61/0.61    spl4_37),
% 1.61/0.61    inference(avatar_contradiction_clause,[],[f509])).
% 1.61/0.61  fof(f509,plain,(
% 1.61/0.61    $false | spl4_37),
% 1.61/0.61    inference(global_subsumption,[],[f494,f508,f501])).
% 1.61/0.61  fof(f501,plain,(
% 1.61/0.61    ~m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))) | spl4_37),
% 1.61/0.61    inference(avatar_component_clause,[],[f500])).
% 1.61/0.61  fof(f494,plain,(
% 1.61/0.61    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))) | ~l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 1.61/0.61    inference(forward_demodulation,[],[f493,f233])).
% 1.61/0.61  fof(f493,plain,(
% 1.61/0.61    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 1.61/0.61    inference(forward_demodulation,[],[f492,f49])).
% 1.61/0.61  fof(f492,plain,(
% 1.61/0.61    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 1.61/0.61    inference(subsumption_resolution,[],[f467,f87])).
% 1.61/0.61  fof(f467,plain,(
% 1.61/0.61    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2) | ~l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 1.61/0.61    inference(resolution,[],[f380,f54])).
% 1.61/0.61  fof(f54,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f36])).
% 1.61/0.61  fof(f36,plain,(
% 1.61/0.61    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.61/0.61    inference(nnf_transformation,[],[f20])).
% 1.61/0.61  fof(f20,plain,(
% 1.61/0.61    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.61/0.61    inference(ennf_transformation,[],[f9])).
% 1.61/0.61  fof(f9,axiom,(
% 1.61/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.61/0.61  % SZS output end Proof for theBenchmark
% 1.61/0.61  % (12390)------------------------------
% 1.61/0.61  % (12390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.61  % (12390)Termination reason: Refutation
% 1.61/0.61  
% 1.61/0.61  % (12390)Memory used [KB]: 11129
% 1.61/0.61  % (12390)Time elapsed: 0.175 s
% 1.61/0.61  % (12390)------------------------------
% 1.61/0.61  % (12390)------------------------------
% 1.61/0.61  % (12377)Success in time 0.242 s
%------------------------------------------------------------------------------
