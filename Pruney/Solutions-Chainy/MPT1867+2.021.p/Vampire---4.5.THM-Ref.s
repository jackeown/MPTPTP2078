%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:08 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 279 expanded)
%              Number of leaves         :   16 (  81 expanded)
%              Depth                    :   17
%              Number of atoms          :  328 (1345 expanded)
%              Number of equality atoms :   36 (  86 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (29446)Termination reason: Refutation not found, incomplete strategy
fof(f242,plain,(
    $false ),
    inference(subsumption_resolution,[],[f241,f94])).

fof(f94,plain,(
    ~ sP0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f93,f47])).

fof(f47,plain,(
    ~ v2_tex_2(sK3,sK2) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f93,plain,
    ( ~ sP0(sK3,sK2)
    | v2_tex_2(sK3,sK2) ),
    inference(resolution,[],[f85,f49])).

fof(f49,plain,(
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

fof(f85,plain,(
    sP1(sK2,sK3) ),
    inference(resolution,[],[f83,f46])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK2,X0) ) ),
    inference(resolution,[],[f56,f44])).

fof(f44,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
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
              & v3_pre_topc(X3,X0)
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
                    & v3_pre_topc(X3,X0)
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
                    & v3_pre_topc(X3,X0)
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
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(f241,plain,(
    sP0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f240,f193])).

fof(f193,plain,(
    ! [X2] : sK3 = k3_xboole_0(sK3,X2) ),
    inference(resolution,[],[f190,f77])).

fof(f77,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k3_xboole_0(X1,X2))
      | k3_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f66,f60])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f190,plain,(
    ! [X0] : r1_tarski(sK3,k3_xboole_0(sK3,X0)) ),
    inference(resolution,[],[f187,f60])).

fof(f187,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3)
      | r1_tarski(sK3,X0) ) ),
    inference(resolution,[],[f182,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f182,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
      | r1_tarski(sK3,X0) ) ),
    inference(resolution,[],[f148,f71])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f148,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(sK3,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | r1_tarski(sK3,X1) ) ),
    inference(resolution,[],[f144,f68])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | r1_tarski(sK3,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f142,f71])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,sK3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | r1_tarski(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f140,f68])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X2,X0) ) ),
    inference(resolution,[],[f137,f45])).

fof(f45,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_xboole_0(X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f62,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X1)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK7(X0,X1,X2),X2)
            & r2_hidden(sK7(X0,X1,X2),X1)
            & m1_subset_1(sK7(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK7(X0,X1,X2),X2)
        & r2_hidden(sK7(X0,X1,X2),X1)
        & m1_subset_1(sK7(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(f240,plain,
    ( sK3 != k3_xboole_0(sK3,sK3)
    | sP0(sK3,sK2) ),
    inference(superposition,[],[f230,f171])).

fof(f171,plain,(
    sK3 = sK4(sK3,sK2) ),
    inference(subsumption_resolution,[],[f170,f94])).

fof(f170,plain,
    ( sP0(sK3,sK2)
    | sK3 = sK4(sK3,sK2) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,
    ( sP0(sK3,sK2)
    | sK3 = sK4(sK3,sK2)
    | sP0(sK3,sK2) ),
    inference(resolution,[],[f153,f78])).

fof(f78,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,sK4(X3,X4))
      | sK4(X3,X4) = X3
      | sP0(X3,X4) ) ),
    inference(resolution,[],[f66,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK4(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(sK4(X0,X1),X0)
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ( k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4
              & v3_pre_topc(sK5(X0,X1,X4),X1)
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
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
            | ~ v3_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(sK4(X0,X1),X0)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
          & v3_pre_topc(X5,X1)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4
        & v3_pre_topc(sK5(X0,X1,X4),X1)
        & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
                | ~ v3_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & r1_tarski(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
                & v3_pre_topc(X5,X1)
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
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f153,plain,(
    ! [X1] :
      ( r1_tarski(sK3,sK4(X1,sK2))
      | sP0(X1,sK2) ) ),
    inference(resolution,[],[f147,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f147,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(sK3,X0) ) ),
    inference(resolution,[],[f144,f46])).

fof(f230,plain,(
    ! [X0] :
      ( sK4(X0,sK2) != k3_xboole_0(X0,sK3)
      | sP0(X0,sK2) ) ),
    inference(forward_demodulation,[],[f229,f90])).

fof(f90,plain,(
    ! [X3] : k9_subset_1(u1_struct_0(sK2),X3,sK3) = k3_xboole_0(X3,sK3) ),
    inference(resolution,[],[f69,f46])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f229,plain,(
    ! [X0] :
      ( sK4(X0,sK2) != k9_subset_1(u1_struct_0(sK2),X0,sK3)
      | sP0(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f226,f46])).

fof(f226,plain,(
    ! [X0] :
      ( sK4(X0,sK2) != k9_subset_1(u1_struct_0(sK2),X0,sK3)
      | sP0(X0,sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f55,f117])).

fof(f117,plain,(
    v3_pre_topc(sK3,sK2) ),
    inference(subsumption_resolution,[],[f115,f46])).

fof(f115,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(sK3,sK2) ),
    inference(resolution,[],[f114,f45])).

fof(f114,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v3_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f113,f43])).

fof(f43,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v3_pre_topc(X0,sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(resolution,[],[f59,f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ v3_pre_topc(X3,X1)
      | k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
      | sP0(X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:08:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (29445)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (29463)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.15/0.51  % (29443)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.15/0.51  % (29460)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.15/0.51  % (29455)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.15/0.51  % (29453)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.15/0.51  % (29444)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.15/0.51  % (29447)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.15/0.52  % (29461)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.15/0.52  % (29443)Refutation found. Thanks to Tanya!
% 1.15/0.52  % SZS status Theorem for theBenchmark
% 1.15/0.52  % (29452)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.15/0.52  % (29442)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.15/0.52  % (29454)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.15/0.52  % (29451)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.15/0.52  % (29446)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.32/0.53  % (29459)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.32/0.53  % (29446)Refutation not found, incomplete strategy% (29446)------------------------------
% 1.32/0.53  % (29446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (29441)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.53  % SZS output start Proof for theBenchmark
% 1.32/0.53  % (29446)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  fof(f242,plain,(
% 1.32/0.53    $false),
% 1.32/0.53    inference(subsumption_resolution,[],[f241,f94])).
% 1.32/0.53  fof(f94,plain,(
% 1.32/0.53    ~sP0(sK3,sK2)),
% 1.32/0.53    inference(subsumption_resolution,[],[f93,f47])).
% 1.32/0.53  fof(f47,plain,(
% 1.32/0.53    ~v2_tex_2(sK3,sK2)),
% 1.32/0.53    inference(cnf_transformation,[],[f29])).
% 1.32/0.53  
% 1.32/0.53  fof(f29,plain,(
% 1.32/0.53    (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f28,f27])).
% 1.32/0.53  fof(f27,plain,(
% 1.32/0.53    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f28,plain,(
% 1.32/0.53    ? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) => (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f14,plain,(
% 1.32/0.53    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.32/0.53    inference(flattening,[],[f13])).
% 1.32/0.53  fof(f13,plain,(
% 1.32/0.53    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.32/0.53    inference(ennf_transformation,[],[f12])).
% 1.32/0.53  fof(f12,plain,(
% 1.32/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.32/0.53    inference(pure_predicate_removal,[],[f11])).
% 1.32/0.53  fof(f11,negated_conjecture,(
% 1.32/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.32/0.53    inference(negated_conjecture,[],[f10])).
% 1.32/0.53  fof(f10,conjecture,(
% 1.32/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 1.32/0.53  fof(f93,plain,(
% 1.32/0.53    ~sP0(sK3,sK2) | v2_tex_2(sK3,sK2)),
% 1.32/0.53    inference(resolution,[],[f85,f49])).
% 1.32/0.53  fof(f49,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v2_tex_2(X1,X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f30])).
% 1.32/0.53  fof(f30,plain,(
% 1.32/0.53    ! [X0,X1] : (((v2_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 1.32/0.53    inference(nnf_transformation,[],[f25])).
% 1.32/0.53  fof(f25,plain,(
% 1.32/0.53    ! [X0,X1] : ((v2_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 1.32/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.32/0.53  fof(f85,plain,(
% 1.32/0.53    sP1(sK2,sK3)),
% 1.32/0.53    inference(resolution,[],[f83,f46])).
% 1.32/0.53  fof(f46,plain,(
% 1.32/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.32/0.53    inference(cnf_transformation,[],[f29])).
% 1.32/0.53  fof(f83,plain,(
% 1.32/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0)) )),
% 1.32/0.53    inference(resolution,[],[f56,f44])).
% 1.32/0.53  fof(f44,plain,(
% 1.32/0.53    l1_pre_topc(sK2)),
% 1.32/0.53    inference(cnf_transformation,[],[f29])).
% 1.32/0.53  fof(f56,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f26])).
% 1.32/0.53  fof(f26,plain,(
% 1.32/0.53    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.53    inference(definition_folding,[],[f16,f25,f24])).
% 1.32/0.53  fof(f24,plain,(
% 1.32/0.53    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.32/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.32/0.53  fof(f16,plain,(
% 1.32/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.53    inference(flattening,[],[f15])).
% 1.32/0.54  fof(f15,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f9])).
% 1.32/0.54  fof(f9,axiom,(
% 1.32/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).
% 1.32/0.54  fof(f241,plain,(
% 1.32/0.54    sP0(sK3,sK2)),
% 1.32/0.54    inference(subsumption_resolution,[],[f240,f193])).
% 1.32/0.54  fof(f193,plain,(
% 1.32/0.54    ( ! [X2] : (sK3 = k3_xboole_0(sK3,X2)) )),
% 1.32/0.54    inference(resolution,[],[f190,f77])).
% 1.32/0.54  fof(f77,plain,(
% 1.32/0.54    ( ! [X2,X1] : (~r1_tarski(X1,k3_xboole_0(X1,X2)) | k3_xboole_0(X1,X2) = X1) )),
% 1.32/0.54    inference(resolution,[],[f66,f60])).
% 1.32/0.54  fof(f60,plain,(
% 1.32/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f2])).
% 1.32/0.54  fof(f2,axiom,(
% 1.32/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.32/0.54  fof(f66,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.32/0.54    inference(cnf_transformation,[],[f41])).
% 1.32/0.54  fof(f41,plain,(
% 1.32/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.32/0.54    inference(flattening,[],[f40])).
% 1.32/0.54  fof(f40,plain,(
% 1.32/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.32/0.54    inference(nnf_transformation,[],[f1])).
% 1.32/0.54  fof(f1,axiom,(
% 1.32/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.32/0.54  fof(f190,plain,(
% 1.32/0.54    ( ! [X0] : (r1_tarski(sK3,k3_xboole_0(sK3,X0))) )),
% 1.32/0.54    inference(resolution,[],[f187,f60])).
% 1.32/0.54  fof(f187,plain,(
% 1.32/0.54    ( ! [X0] : (~r1_tarski(X0,sK3) | r1_tarski(sK3,X0)) )),
% 1.32/0.54    inference(resolution,[],[f182,f68])).
% 1.32/0.54  fof(f68,plain,(
% 1.32/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f42])).
% 1.32/0.54  fof(f42,plain,(
% 1.32/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.32/0.54    inference(nnf_transformation,[],[f5])).
% 1.32/0.54  fof(f5,axiom,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.32/0.54  fof(f182,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK3)) | r1_tarski(sK3,X0)) )),
% 1.32/0.54    inference(resolution,[],[f148,f71])).
% 1.32/0.54  fof(f71,plain,(
% 1.32/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.32/0.54    inference(equality_resolution,[],[f65])).
% 1.32/0.54  fof(f65,plain,(
% 1.32/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.32/0.54    inference(cnf_transformation,[],[f41])).
% 1.32/0.54  fof(f148,plain,(
% 1.32/0.54    ( ! [X2,X1] : (~r1_tarski(sK3,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | r1_tarski(sK3,X1)) )),
% 1.32/0.54    inference(resolution,[],[f144,f68])).
% 1.32/0.54  fof(f144,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X1)) | r1_tarski(sK3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.32/0.54    inference(resolution,[],[f142,f71])).
% 1.32/0.54  fof(f142,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | r1_tarski(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.32/0.54    inference(resolution,[],[f140,f68])).
% 1.32/0.54  fof(f140,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(sK3)) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X2,X0)) )),
% 1.32/0.54    inference(resolution,[],[f137,f45])).
% 1.32/0.54  fof(f45,plain,(
% 1.32/0.54    v1_xboole_0(sK3)),
% 1.32/0.54    inference(cnf_transformation,[],[f29])).
% 1.32/0.54  fof(f137,plain,(
% 1.32/0.54    ( ! [X2,X0,X3,X1] : (~v1_xboole_0(X3) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X3)) | r1_tarski(X0,X1)) )),
% 1.32/0.54    inference(resolution,[],[f62,f70])).
% 1.32/0.54  fof(f70,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f23])).
% 1.32/0.54  fof(f23,plain,(
% 1.32/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.32/0.54    inference(ennf_transformation,[],[f6])).
% 1.32/0.54  fof(f6,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.32/0.54  fof(f62,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X1) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f39])).
% 1.32/0.54  fof(f39,plain,(
% 1.32/0.54    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK7(X0,X1,X2),X2) & r2_hidden(sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f38])).
% 1.32/0.54  fof(f38,plain,(
% 1.32/0.54    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK7(X0,X1,X2),X2) & r2_hidden(sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),X0)))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f21,plain,(
% 1.32/0.54    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(flattening,[],[f20])).
% 1.32/0.54  fof(f20,plain,(
% 1.32/0.54    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f4])).
% 1.32/0.54  fof(f4,axiom,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).
% 1.32/0.54  fof(f240,plain,(
% 1.32/0.54    sK3 != k3_xboole_0(sK3,sK3) | sP0(sK3,sK2)),
% 1.32/0.54    inference(superposition,[],[f230,f171])).
% 1.32/0.54  fof(f171,plain,(
% 1.32/0.54    sK3 = sK4(sK3,sK2)),
% 1.32/0.54    inference(subsumption_resolution,[],[f170,f94])).
% 1.32/0.54  fof(f170,plain,(
% 1.32/0.54    sP0(sK3,sK2) | sK3 = sK4(sK3,sK2)),
% 1.32/0.54    inference(duplicate_literal_removal,[],[f167])).
% 1.32/0.54  fof(f167,plain,(
% 1.32/0.54    sP0(sK3,sK2) | sK3 = sK4(sK3,sK2) | sP0(sK3,sK2)),
% 1.32/0.54    inference(resolution,[],[f153,f78])).
% 1.32/0.54  fof(f78,plain,(
% 1.32/0.54    ( ! [X4,X3] : (~r1_tarski(X3,sK4(X3,X4)) | sK4(X3,X4) = X3 | sP0(X3,X4)) )),
% 1.32/0.54    inference(resolution,[],[f66,f54])).
% 1.32/0.54  fof(f54,plain,(
% 1.32/0.54    ( ! [X0,X1] : (r1_tarski(sK4(X0,X1),X0) | sP0(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f35])).
% 1.32/0.54  fof(f35,plain,(
% 1.32/0.54    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK4(X0,X1),X0) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4 & v3_pre_topc(sK5(X0,X1,X4),X1) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 1.32/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f34,f33])).
% 1.32/0.54  fof(f33,plain,(
% 1.32/0.54    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK4(X0,X1),X0) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f34,plain,(
% 1.32/0.54    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v3_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4 & v3_pre_topc(sK5(X0,X1,X4),X1) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f32,plain,(
% 1.32/0.54    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v3_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 1.32/0.54    inference(rectify,[],[f31])).
% 1.32/0.54  fof(f31,plain,(
% 1.32/0.54    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 1.32/0.54    inference(nnf_transformation,[],[f24])).
% 1.32/0.54  fof(f153,plain,(
% 1.32/0.54    ( ! [X1] : (r1_tarski(sK3,sK4(X1,sK2)) | sP0(X1,sK2)) )),
% 1.32/0.54    inference(resolution,[],[f147,f53])).
% 1.32/0.54  fof(f53,plain,(
% 1.32/0.54    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | sP0(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f35])).
% 1.32/0.54  fof(f147,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(sK3,X0)) )),
% 1.32/0.54    inference(resolution,[],[f144,f46])).
% 1.32/0.54  fof(f230,plain,(
% 1.32/0.54    ( ! [X0] : (sK4(X0,sK2) != k3_xboole_0(X0,sK3) | sP0(X0,sK2)) )),
% 1.32/0.54    inference(forward_demodulation,[],[f229,f90])).
% 1.32/0.54  fof(f90,plain,(
% 1.32/0.54    ( ! [X3] : (k9_subset_1(u1_struct_0(sK2),X3,sK3) = k3_xboole_0(X3,sK3)) )),
% 1.32/0.54    inference(resolution,[],[f69,f46])).
% 1.32/0.54  fof(f69,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f22])).
% 1.32/0.54  fof(f22,plain,(
% 1.32/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f3])).
% 1.32/0.54  fof(f3,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.32/0.54  fof(f229,plain,(
% 1.32/0.54    ( ! [X0] : (sK4(X0,sK2) != k9_subset_1(u1_struct_0(sK2),X0,sK3) | sP0(X0,sK2)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f226,f46])).
% 1.32/0.54  fof(f226,plain,(
% 1.32/0.54    ( ! [X0] : (sK4(X0,sK2) != k9_subset_1(u1_struct_0(sK2),X0,sK3) | sP0(X0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.32/0.54    inference(resolution,[],[f55,f117])).
% 1.32/0.54  fof(f117,plain,(
% 1.32/0.54    v3_pre_topc(sK3,sK2)),
% 1.32/0.54    inference(subsumption_resolution,[],[f115,f46])).
% 1.32/0.54  fof(f115,plain,(
% 1.32/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(sK3,sK2)),
% 1.32/0.54    inference(resolution,[],[f114,f45])).
% 1.32/0.54  fof(f114,plain,(
% 1.32/0.54    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(X0,sK2)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f113,f43])).
% 1.32/0.54  fof(f43,plain,(
% 1.32/0.54    v2_pre_topc(sK2)),
% 1.32/0.54    inference(cnf_transformation,[],[f29])).
% 1.32/0.54  fof(f113,plain,(
% 1.32/0.54    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(X0,sK2) | ~v2_pre_topc(sK2)) )),
% 1.32/0.54    inference(resolution,[],[f59,f44])).
% 1.32/0.54  fof(f59,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f19])).
% 1.32/0.54  fof(f19,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.32/0.54    inference(flattening,[],[f18])).
% 1.32/0.54  fof(f18,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f7])).
% 1.32/0.54  fof(f7,axiom,(
% 1.32/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).
% 1.32/0.54  fof(f55,plain,(
% 1.32/0.54    ( ! [X0,X3,X1] : (~v3_pre_topc(X3,X1) | k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | sP0(X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f35])).
% 1.32/0.54  % SZS output end Proof for theBenchmark
% 1.32/0.54  % (29443)------------------------------
% 1.32/0.54  % (29443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (29443)Termination reason: Refutation
% 1.32/0.54  
% 1.32/0.54  % (29443)Memory used [KB]: 6396
% 1.32/0.54  % (29443)Time elapsed: 0.097 s
% 1.32/0.54  % (29443)------------------------------
% 1.32/0.54  % (29443)------------------------------
% 1.32/0.54  % (29446)Memory used [KB]: 10618
% 1.32/0.54  % (29446)Time elapsed: 0.095 s
% 1.32/0.54  % (29446)------------------------------
% 1.32/0.54  % (29446)------------------------------
% 1.32/0.54  % (29439)Success in time 0.172 s
%------------------------------------------------------------------------------
