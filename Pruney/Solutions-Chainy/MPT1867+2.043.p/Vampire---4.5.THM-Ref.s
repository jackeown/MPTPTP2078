%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:11 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 220 expanded)
%              Number of leaves         :   17 (  66 expanded)
%              Depth                    :   16
%              Number of atoms          :  302 ( 992 expanded)
%              Number of equality atoms :   35 (  63 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f377,plain,(
    $false ),
    inference(subsumption_resolution,[],[f376,f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f376,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f375,f135])).

fof(f135,plain,(
    v4_pre_topc(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f133,f51])).

fof(f133,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(k1_xboole_0,sK2) ),
    inference(resolution,[],[f132,f76])).

fof(f76,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f48,f75])).

fof(f75,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f61,f48])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f48,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & v1_xboole_0(X1) )
   => ( ~ v2_tex_2(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f132,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v4_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f131,f46])).

fof(f46,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f131,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v4_pre_topc(X0,sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(resolution,[],[f62,f47])).

fof(f47,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f375,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f374,f106])).

fof(f106,plain,(
    ~ sP0(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f105,f78])).

fof(f78,plain,(
    ~ v2_tex_2(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f50,f75])).

fof(f50,plain,(
    ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f105,plain,
    ( ~ sP0(k1_xboole_0,sK2)
    | v2_tex_2(k1_xboole_0,sK2) ),
    inference(resolution,[],[f103,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v2_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f103,plain,(
    sP1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f102,f51])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK2,X0) ) ),
    inference(resolution,[],[f60,f47])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f16,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ? [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
              & v4_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

fof(f374,plain,
    ( sP0(k1_xboole_0,sK2)
    | ~ v4_pre_topc(k1_xboole_0,sK2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(trivial_inequality_removal,[],[f373])).

fof(f373,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sP0(k1_xboole_0,sK2)
    | ~ v4_pre_topc(k1_xboole_0,sK2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(superposition,[],[f372,f107])).

fof(f107,plain,(
    k1_xboole_0 = sK4(k1_xboole_0,sK2) ),
    inference(resolution,[],[f106,f89])).

fof(f89,plain,(
    ! [X0] :
      ( sP0(k1_xboole_0,X0)
      | k1_xboole_0 = sK4(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f87,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK4(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
              | ~ v4_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(sK4(X0,X1),X0)
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ( k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4
              & v4_pre_topc(sK5(X0,X1,X4),X1)
              & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f34,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
              | ~ v4_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
            | ~ v4_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(sK4(X0,X1),X0)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
          & v4_pre_topc(X5,X1)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4
        & v4_pre_topc(sK5(X0,X1,X4),X1)
        & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
                | ~ v4_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & r1_tarski(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
                & v4_pre_topc(X5,X1)
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                | ~ v4_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                & v4_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f87,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f86,f76])).

fof(f86,plain,(
    ! [X4,X3] :
      ( ~ v1_xboole_0(X4)
      | X3 = X4
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f67,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f69,f63])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
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

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
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

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f372,plain,(
    ! [X0,X1] :
      ( sK4(X1,X0) != X1
      | sP0(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(superposition,[],[f59,f113])).

fof(f113,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X1) = X1 ),
    inference(resolution,[],[f71,f51])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
      | sP0(X0,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:55:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (26132)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.49  % (26139)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (26153)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (26145)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (26153)Refutation not found, incomplete strategy% (26153)------------------------------
% 0.21/0.51  % (26153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26153)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26153)Memory used [KB]: 1791
% 0.21/0.51  % (26153)Time elapsed: 0.065 s
% 0.21/0.51  % (26153)------------------------------
% 0.21/0.51  % (26153)------------------------------
% 0.21/0.51  % (26137)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (26133)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.52  % (26138)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.30/0.52  % (26134)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.52  % (26149)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.30/0.52  % (26134)Refutation not found, incomplete strategy% (26134)------------------------------
% 1.30/0.52  % (26134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.52  % (26134)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.52  
% 1.30/0.52  % (26134)Memory used [KB]: 10618
% 1.30/0.52  % (26134)Time elapsed: 0.119 s
% 1.30/0.52  % (26134)------------------------------
% 1.30/0.52  % (26134)------------------------------
% 1.30/0.53  % (26147)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.30/0.53  % (26139)Refutation found. Thanks to Tanya!
% 1.30/0.53  % SZS status Theorem for theBenchmark
% 1.30/0.53  % SZS output start Proof for theBenchmark
% 1.30/0.53  fof(f377,plain,(
% 1.30/0.53    $false),
% 1.30/0.53    inference(subsumption_resolution,[],[f376,f51])).
% 1.30/0.53  fof(f51,plain,(
% 1.30/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f6])).
% 1.30/0.53  fof(f6,axiom,(
% 1.30/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.30/0.53  fof(f376,plain,(
% 1.30/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.30/0.53    inference(subsumption_resolution,[],[f375,f135])).
% 1.30/0.53  fof(f135,plain,(
% 1.30/0.53    v4_pre_topc(k1_xboole_0,sK2)),
% 1.30/0.53    inference(subsumption_resolution,[],[f133,f51])).
% 1.30/0.53  fof(f133,plain,(
% 1.30/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) | v4_pre_topc(k1_xboole_0,sK2)),
% 1.30/0.53    inference(resolution,[],[f132,f76])).
% 1.30/0.53  fof(f76,plain,(
% 1.30/0.53    v1_xboole_0(k1_xboole_0)),
% 1.30/0.53    inference(backward_demodulation,[],[f48,f75])).
% 1.30/0.53  fof(f75,plain,(
% 1.30/0.53    k1_xboole_0 = sK3),
% 1.30/0.53    inference(resolution,[],[f61,f48])).
% 1.30/0.53  fof(f61,plain,(
% 1.30/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.30/0.53    inference(cnf_transformation,[],[f17])).
% 1.30/0.53  fof(f17,plain,(
% 1.30/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.30/0.53    inference(ennf_transformation,[],[f3])).
% 1.30/0.53  fof(f3,axiom,(
% 1.30/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.30/0.53  fof(f48,plain,(
% 1.30/0.53    v1_xboole_0(sK3)),
% 1.30/0.53    inference(cnf_transformation,[],[f29])).
% 1.30/0.53  fof(f29,plain,(
% 1.30/0.53    (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f28,f27])).
% 1.30/0.53  fof(f27,plain,(
% 1.30/0.53    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f28,plain,(
% 1.30/0.53    ? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) => (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f14,plain,(
% 1.30/0.53    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.30/0.53    inference(flattening,[],[f13])).
% 1.30/0.53  fof(f13,plain,(
% 1.30/0.53    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.30/0.53    inference(ennf_transformation,[],[f12])).
% 1.30/0.53  fof(f12,plain,(
% 1.30/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.30/0.53    inference(pure_predicate_removal,[],[f11])).
% 1.30/0.53  fof(f11,negated_conjecture,(
% 1.30/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.30/0.53    inference(negated_conjecture,[],[f10])).
% 1.30/0.53  fof(f10,conjecture,(
% 1.30/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).
% 1.30/0.53  fof(f132,plain,(
% 1.30/0.53    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v4_pre_topc(X0,sK2)) )),
% 1.30/0.53    inference(subsumption_resolution,[],[f131,f46])).
% 1.30/0.53  fof(f46,plain,(
% 1.30/0.53    v2_pre_topc(sK2)),
% 1.30/0.53    inference(cnf_transformation,[],[f29])).
% 1.30/0.53  fof(f131,plain,(
% 1.30/0.53    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v4_pre_topc(X0,sK2) | ~v2_pre_topc(sK2)) )),
% 1.30/0.53    inference(resolution,[],[f62,f47])).
% 1.30/0.53  fof(f47,plain,(
% 1.30/0.53    l1_pre_topc(sK2)),
% 1.30/0.53    inference(cnf_transformation,[],[f29])).
% 1.30/0.53  fof(f62,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f19])).
% 1.30/0.53  fof(f19,plain,(
% 1.30/0.53    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.30/0.53    inference(flattening,[],[f18])).
% 1.30/0.53  fof(f18,plain,(
% 1.30/0.53    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.30/0.53    inference(ennf_transformation,[],[f8])).
% 1.30/0.53  fof(f8,axiom,(
% 1.30/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 1.30/0.53  fof(f375,plain,(
% 1.30/0.53    ~v4_pre_topc(k1_xboole_0,sK2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.30/0.53    inference(subsumption_resolution,[],[f374,f106])).
% 1.30/0.53  fof(f106,plain,(
% 1.30/0.53    ~sP0(k1_xboole_0,sK2)),
% 1.30/0.53    inference(subsumption_resolution,[],[f105,f78])).
% 1.30/0.53  fof(f78,plain,(
% 1.30/0.53    ~v2_tex_2(k1_xboole_0,sK2)),
% 1.30/0.53    inference(backward_demodulation,[],[f50,f75])).
% 1.30/0.53  fof(f50,plain,(
% 1.30/0.53    ~v2_tex_2(sK3,sK2)),
% 1.30/0.53    inference(cnf_transformation,[],[f29])).
% 1.30/0.53  fof(f105,plain,(
% 1.30/0.53    ~sP0(k1_xboole_0,sK2) | v2_tex_2(k1_xboole_0,sK2)),
% 1.30/0.53    inference(resolution,[],[f103,f53])).
% 1.30/0.53  fof(f53,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v2_tex_2(X1,X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f30])).
% 1.30/0.53  fof(f30,plain,(
% 1.30/0.53    ! [X0,X1] : (((v2_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 1.30/0.53    inference(nnf_transformation,[],[f25])).
% 1.30/0.53  fof(f25,plain,(
% 1.30/0.53    ! [X0,X1] : ((v2_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 1.30/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.30/0.53  fof(f103,plain,(
% 1.30/0.53    sP1(sK2,k1_xboole_0)),
% 1.30/0.53    inference(resolution,[],[f102,f51])).
% 1.30/0.53  fof(f102,plain,(
% 1.30/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0)) )),
% 1.30/0.53    inference(resolution,[],[f60,f47])).
% 1.30/0.53  fof(f60,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f26])).
% 1.30/0.53  fof(f26,plain,(
% 1.30/0.53    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.30/0.53    inference(definition_folding,[],[f16,f25,f24])).
% 1.30/0.53  fof(f24,plain,(
% 1.30/0.53    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.30/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.30/0.53  fof(f16,plain,(
% 1.30/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.30/0.53    inference(flattening,[],[f15])).
% 1.30/0.53  fof(f15,plain,(
% 1.30/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.30/0.53    inference(ennf_transformation,[],[f9])).
% 1.30/0.53  fof(f9,axiom,(
% 1.30/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).
% 1.30/0.53  fof(f374,plain,(
% 1.30/0.53    sP0(k1_xboole_0,sK2) | ~v4_pre_topc(k1_xboole_0,sK2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.30/0.53    inference(trivial_inequality_removal,[],[f373])).
% 1.30/0.53  fof(f373,plain,(
% 1.30/0.53    k1_xboole_0 != k1_xboole_0 | sP0(k1_xboole_0,sK2) | ~v4_pre_topc(k1_xboole_0,sK2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.30/0.53    inference(superposition,[],[f372,f107])).
% 1.30/0.53  fof(f107,plain,(
% 1.30/0.53    k1_xboole_0 = sK4(k1_xboole_0,sK2)),
% 1.30/0.53    inference(resolution,[],[f106,f89])).
% 1.30/0.53  fof(f89,plain,(
% 1.30/0.53    ( ! [X0] : (sP0(k1_xboole_0,X0) | k1_xboole_0 = sK4(k1_xboole_0,X0)) )),
% 1.30/0.53    inference(resolution,[],[f87,f58])).
% 1.30/0.53  fof(f58,plain,(
% 1.30/0.53    ( ! [X0,X1] : (r1_tarski(sK4(X0,X1),X0) | sP0(X0,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f35])).
% 1.30/0.53  fof(f35,plain,(
% 1.30/0.53    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK4(X0,X1),X0) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4 & v4_pre_topc(sK5(X0,X1,X4),X1) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f34,f33])).
% 1.30/0.53  fof(f33,plain,(
% 1.30/0.53    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK4(X0,X1),X0) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f34,plain,(
% 1.30/0.53    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v4_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4 & v4_pre_topc(sK5(X0,X1,X4),X1) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f32,plain,(
% 1.30/0.53    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v4_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 1.30/0.53    inference(rectify,[],[f31])).
% 1.30/0.53  fof(f31,plain,(
% 1.30/0.53    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 1.30/0.53    inference(nnf_transformation,[],[f24])).
% 1.30/0.53  fof(f87,plain,(
% 1.30/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.30/0.53    inference(resolution,[],[f86,f76])).
% 1.30/0.53  fof(f86,plain,(
% 1.30/0.53    ( ! [X4,X3] : (~v1_xboole_0(X4) | X3 = X4 | ~r1_tarski(X3,X4)) )),
% 1.30/0.53    inference(resolution,[],[f67,f81])).
% 1.30/0.53  fof(f81,plain,(
% 1.30/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 1.30/0.53    inference(resolution,[],[f69,f63])).
% 1.30/0.53  fof(f63,plain,(
% 1.30/0.53    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f39])).
% 1.30/0.53  fof(f39,plain,(
% 1.30/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).
% 1.30/0.53  fof(f38,plain,(
% 1.30/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f37,plain,(
% 1.30/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.30/0.53    inference(rectify,[],[f36])).
% 1.30/0.53  fof(f36,plain,(
% 1.30/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.30/0.53    inference(nnf_transformation,[],[f1])).
% 1.30/0.53  fof(f1,axiom,(
% 1.30/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.30/0.53  fof(f69,plain,(
% 1.30/0.53    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f45])).
% 1.30/0.53  fof(f45,plain,(
% 1.30/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f43,f44])).
% 1.30/0.53  fof(f44,plain,(
% 1.30/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f43,plain,(
% 1.30/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.30/0.53    inference(rectify,[],[f42])).
% 1.30/0.53  fof(f42,plain,(
% 1.30/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.30/0.53    inference(nnf_transformation,[],[f20])).
% 1.30/0.53  fof(f20,plain,(
% 1.30/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.30/0.53    inference(ennf_transformation,[],[f2])).
% 1.30/0.53  fof(f2,axiom,(
% 1.30/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.30/0.53  fof(f67,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.30/0.53    inference(cnf_transformation,[],[f41])).
% 1.30/0.53  fof(f41,plain,(
% 1.30/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.30/0.53    inference(flattening,[],[f40])).
% 1.30/0.53  fof(f40,plain,(
% 1.30/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.30/0.53    inference(nnf_transformation,[],[f4])).
% 1.30/0.53  fof(f4,axiom,(
% 1.30/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.30/0.53  fof(f372,plain,(
% 1.30/0.53    ( ! [X0,X1] : (sK4(X1,X0) != X1 | sP0(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.30/0.53    inference(superposition,[],[f59,f113])).
% 1.30/0.53  fof(f113,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k9_subset_1(X0,X1,X1) = X1) )),
% 1.30/0.53    inference(resolution,[],[f71,f51])).
% 1.30/0.53  fof(f71,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X1) = X1) )),
% 1.30/0.53    inference(cnf_transformation,[],[f21])).
% 1.30/0.53  fof(f21,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.30/0.53    inference(ennf_transformation,[],[f5])).
% 1.30/0.53  fof(f5,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 1.30/0.53  fof(f59,plain,(
% 1.30/0.53    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | sP0(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f35])).
% 1.30/0.53  % SZS output end Proof for theBenchmark
% 1.30/0.53  % (26139)------------------------------
% 1.30/0.53  % (26139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (26139)Termination reason: Refutation
% 1.30/0.53  
% 1.30/0.53  % (26139)Memory used [KB]: 6524
% 1.30/0.53  % (26139)Time elapsed: 0.106 s
% 1.30/0.53  % (26139)------------------------------
% 1.30/0.53  % (26139)------------------------------
% 1.30/0.53  % (26142)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.30/0.53  % (26131)Success in time 0.172 s
%------------------------------------------------------------------------------
