%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 147 expanded)
%              Number of leaves         :   17 (  46 expanded)
%              Depth                    :   16
%              Number of atoms          :  271 ( 626 expanded)
%              Number of equality atoms :   33 (  44 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f280,plain,(
    $false ),
    inference(subsumption_resolution,[],[f279,f43])).

fof(f43,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f31])).

% (11370)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f31,plain,
    ( ~ v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK3)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        & v1_xboole_0(X1) )
   => ( ~ v2_tex_2(sK4,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
      & v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f279,plain,(
    ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f278,f44])).

fof(f44,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f278,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f277,f45])).

fof(f45,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f277,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f276,f180])).

fof(f180,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f63,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f49,f61])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f276,plain,(
    ~ v4_pre_topc(sK4,sK3) ),
    inference(subsumption_resolution,[],[f274,f45])).

fof(f274,plain,
    ( ~ v4_pre_topc(sK4,sK3)
    | ~ v1_xboole_0(sK4) ),
    inference(resolution,[],[f272,f104])).

fof(f104,plain,(
    ~ sP1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f102,f47])).

fof(f47,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f102,plain,
    ( ~ sP1(sK3,sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(resolution,[],[f101,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ sP1(X1,X0)
      | v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v2_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ( v2_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f101,plain,(
    sP2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f99,f44])).

fof(f99,plain,
    ( sP2(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f60,f46])).

fof(f46,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f17,f27,f26,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ? [X3] :
          ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( sP0(X2,X1,X0)
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

fof(f272,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ v4_pre_topc(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f267,f61])).

fof(f267,plain,(
    ! [X0] :
      ( sP1(X0,k1_xboole_0)
      | ~ v4_pre_topc(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f266,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ sP0(k1_xboole_0,k1_xboole_0,X0)
      | sP1(X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ sP0(k1_xboole_0,k1_xboole_0,X0)
      | sP1(X0,k1_xboole_0)
      | sP1(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f55,f82])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK5(X0,k1_xboole_0)
      | sP1(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f54,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK5(X0,X1),X1)
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ~ sP0(sK5(X0,X1),X1,X0)
          & r1_tarski(sK5(X0,X1),X1)
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( sP0(X3,X1,X0)
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ sP0(X2,X1,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ sP0(sK5(X0,X1),X1,X0)
        & r1_tarski(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ~ sP0(X2,X1,X0)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( sP0(X3,X1,X0)
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ~ sP0(X2,X1,X0)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( sP0(X2,X1,X0)
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK5(X0,X1),X1,X0)
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f266,plain,(
    ! [X10,X9] :
      ( sP0(k1_xboole_0,X10,X9)
      | ~ v4_pre_topc(k1_xboole_0,X9) ) ),
    inference(subsumption_resolution,[],[f263,f49])).

fof(f263,plain,(
    ! [X10,X9] :
      ( sP0(k1_xboole_0,X10,X9)
      | ~ v4_pre_topc(k1_xboole_0,X9)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X9))) ) ),
    inference(superposition,[],[f71,f234])).

fof(f234,plain,(
    ! [X15,X16] : k1_xboole_0 = k9_subset_1(X16,X15,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f217,f49])).

fof(f217,plain,(
    ! [X15,X16] :
      ( k1_xboole_0 = k9_subset_1(X16,X15,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)) ) ),
    inference(superposition,[],[f70,f117])).

fof(f117,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f69,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f62,f64])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f65,f66,f66])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f67,f66])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f71,plain,(
    ! [X2,X3,X1] :
      ( sP0(k9_subset_1(u1_struct_0(X2),X1,X3),X1,X2)
      | ~ v4_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | k9_subset_1(u1_struct_0(X2),X1,X3) != X0
      | ~ v4_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X2),X1,X3) != X0
            | ~ v4_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ( k9_subset_1(u1_struct_0(X2),X1,sK6(X0,X1,X2)) = X0
          & v4_pre_topc(sK6(X0,X1,X2),X2)
          & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X2),X1,X4) = X0
          & v4_pre_topc(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( k9_subset_1(u1_struct_0(X2),X1,sK6(X0,X1,X2)) = X0
        & v4_pre_topc(sK6(X0,X1,X2),X2)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X2),X1,X3) != X0
            | ~ v4_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ? [X4] :
            ( k9_subset_1(u1_struct_0(X2),X1,X4) = X0
            & v4_pre_topc(X4,X2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
            & v4_pre_topc(X3,X0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (11375)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (11356)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (11375)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (11367)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (11352)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (11356)Refutation not found, incomplete strategy% (11356)------------------------------
% 0.20/0.54  % (11356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11356)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11356)Memory used [KB]: 10618
% 0.20/0.54  % (11356)Time elapsed: 0.125 s
% 0.20/0.54  % (11356)------------------------------
% 0.20/0.54  % (11356)------------------------------
% 0.20/0.54  % (11352)Refutation not found, incomplete strategy% (11352)------------------------------
% 0.20/0.54  % (11352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11352)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11352)Memory used [KB]: 6268
% 0.20/0.54  % (11352)Time elapsed: 0.131 s
% 0.20/0.54  % (11352)------------------------------
% 0.20/0.54  % (11352)------------------------------
% 0.20/0.54  % (11358)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f280,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f279,f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    v2_pre_topc(sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  % (11370)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    (~v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f30,f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ? [X1] : (~v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) => (~v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,negated_conjecture,(
% 0.20/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.55    inference(negated_conjecture,[],[f12])).
% 0.20/0.55  fof(f12,conjecture,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.20/0.55  fof(f279,plain,(
% 0.20/0.55    ~v2_pre_topc(sK3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f278,f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    l1_pre_topc(sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f278,plain,(
% 0.20/0.55    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f277,f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    v1_xboole_0(sK4)),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f277,plain,(
% 0.20/0.55    ~v1_xboole_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 0.20/0.55    inference(resolution,[],[f276,f180])).
% 0.20/0.55  fof(f180,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f63,f73])).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X0)) )),
% 0.20/0.55    inference(superposition,[],[f49,f61])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.20/0.55  fof(f276,plain,(
% 0.20/0.55    ~v4_pre_topc(sK4,sK3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f274,f45])).
% 0.20/0.55  fof(f274,plain,(
% 0.20/0.55    ~v4_pre_topc(sK4,sK3) | ~v1_xboole_0(sK4)),
% 0.20/0.55    inference(resolution,[],[f272,f104])).
% 0.20/0.55  fof(f104,plain,(
% 0.20/0.55    ~sP1(sK3,sK4)),
% 0.20/0.55    inference(subsumption_resolution,[],[f102,f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ~v2_tex_2(sK4,sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f102,plain,(
% 0.20/0.55    ~sP1(sK3,sK4) | v2_tex_2(sK4,sK3)),
% 0.20/0.55    inference(resolution,[],[f101,f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~sP2(X0,X1) | ~sP1(X1,X0) | v2_tex_2(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0,X1] : (((v2_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v2_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 0.20/0.55    inference(rectify,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X1,X0] : (((v2_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v2_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 0.20/0.55    inference(nnf_transformation,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X1,X0] : ((v2_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 0.20/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.55  fof(f101,plain,(
% 0.20/0.55    sP2(sK4,sK3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f99,f44])).
% 0.20/0.55  fof(f99,plain,(
% 0.20/0.55    sP2(sK4,sK3) | ~l1_pre_topc(sK3)),
% 0.20/0.55    inference(resolution,[],[f60,f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(definition_folding,[],[f17,f27,f26,f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> ? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (sP0(X2,X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).
% 0.20/0.55  fof(f272,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sP1(X1,X0) | ~v4_pre_topc(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.55    inference(superposition,[],[f267,f61])).
% 0.20/0.55  fof(f267,plain,(
% 0.20/0.55    ( ! [X0] : (sP1(X0,k1_xboole_0) | ~v4_pre_topc(k1_xboole_0,X0)) )),
% 0.20/0.55    inference(resolution,[],[f266,f93])).
% 0.20/0.55  fof(f93,plain,(
% 0.20/0.55    ( ! [X0] : (~sP0(k1_xboole_0,k1_xboole_0,X0) | sP1(X0,k1_xboole_0)) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f92])).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    ( ! [X0] : (~sP0(k1_xboole_0,k1_xboole_0,X0) | sP1(X0,k1_xboole_0) | sP1(X0,k1_xboole_0)) )),
% 0.20/0.55    inference(superposition,[],[f55,f82])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = sK5(X0,k1_xboole_0) | sP1(X0,k1_xboole_0)) )),
% 0.20/0.55    inference(resolution,[],[f54,f62])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.55    inference(ennf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(sK5(X0,X1),X1) | sP1(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(sK5(X0,X1),X1,X0) & r1_tarski(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (sP0(X3,X1,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0,X1)))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : (~sP0(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~sP0(sK5(X0,X1),X1,X0) & r1_tarski(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : (~sP0(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (sP0(X3,X1,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0,X1)))),
% 0.20/0.55    inference(rectify,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : (~sP0(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (sP0(X2,X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0,X1)))),
% 0.20/0.55    inference(nnf_transformation,[],[f26])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~sP0(sK5(X0,X1),X1,X0) | sP1(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f266,plain,(
% 0.20/0.55    ( ! [X10,X9] : (sP0(k1_xboole_0,X10,X9) | ~v4_pre_topc(k1_xboole_0,X9)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f263,f49])).
% 0.20/0.55  fof(f263,plain,(
% 0.20/0.55    ( ! [X10,X9] : (sP0(k1_xboole_0,X10,X9) | ~v4_pre_topc(k1_xboole_0,X9) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X9)))) )),
% 0.20/0.55    inference(superposition,[],[f71,f234])).
% 0.20/0.55  fof(f234,plain,(
% 0.20/0.55    ( ! [X15,X16] : (k1_xboole_0 = k9_subset_1(X16,X15,k1_xboole_0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f217,f49])).
% 0.20/0.55  fof(f217,plain,(
% 0.20/0.55    ( ! [X15,X16] : (k1_xboole_0 = k9_subset_1(X16,X15,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16))) )),
% 0.20/0.55    inference(superposition,[],[f70,f117])).
% 0.20/0.55  fof(f117,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.55    inference(superposition,[],[f69,f75])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.55    inference(resolution,[],[f62,f64])).
% 0.20/0.55  fof(f64,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f65,f66,f66])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f67,f66])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X2,X3,X1] : (sP0(k9_subset_1(u1_struct_0(X2),X1,X3),X1,X2) | ~v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.20/0.55    inference(equality_resolution,[],[f59])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | k9_subset_1(u1_struct_0(X2),X1,X3) != X0 | ~v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (k9_subset_1(u1_struct_0(X2),X1,X3) != X0 | ~v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & ((k9_subset_1(u1_struct_0(X2),X1,sK6(X0,X1,X2)) = X0 & v4_pre_topc(sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X2),X1,X4) = X0 & v4_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) => (k9_subset_1(u1_struct_0(X2),X1,sK6(X0,X1,X2)) = X0 & v4_pre_topc(sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (k9_subset_1(u1_struct_0(X2),X1,X3) != X0 | ~v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (? [X4] : (k9_subset_1(u1_struct_0(X2),X1,X4) = X0 & v4_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 0.20/0.55    inference(rectify,[],[f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | ! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X2,X1,X0)))),
% 0.20/0.55    inference(nnf_transformation,[],[f25])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (11375)------------------------------
% 0.20/0.55  % (11375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (11375)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (11375)Memory used [KB]: 6268
% 0.20/0.55  % (11375)Time elapsed: 0.125 s
% 0.20/0.55  % (11375)------------------------------
% 0.20/0.55  % (11375)------------------------------
% 0.20/0.55  % (11347)Success in time 0.19 s
%------------------------------------------------------------------------------
