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
% DateTime   : Thu Dec  3 13:21:07 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 152 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  309 ( 703 expanded)
%              Number of equality atoms :   32 (  36 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f262,f268,f278])).

fof(f278,plain,(
    ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f276,f54])).

fof(f54,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f17,f32,f31])).

fof(f31,plain,
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

fof(f32,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK3)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        & v1_xboole_0(X1) )
   => ( ~ v2_tex_2(sK4,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
      & v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f276,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f275,f143])).

fof(f143,plain,(
    ~ sP1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f141,f56])).

fof(f56,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f141,plain,
    ( ~ sP1(sK3,sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(resolution,[],[f140,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ sP1(X1,X0)
      | v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v2_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ( v2_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f140,plain,(
    sP2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f137,f53])).

fof(f53,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f137,plain,
    ( sP2(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f70,f55])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f19,f29,f28,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ? [X3] :
          ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( sP0(X2,X1,X0)
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f275,plain,
    ( sP1(sK3,sK4)
    | ~ v1_xboole_0(sK4)
    | ~ spl8_2 ),
    inference(resolution,[],[f261,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X0,X1)
      | sP1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f132,f71])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f132,plain,(
    ! [X1] :
      ( ~ sP0(k1_xboole_0,k1_xboole_0,X1)
      | sP1(X1,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,(
    ! [X1] :
      ( ~ sP0(k1_xboole_0,k1_xboole_0,X1)
      | sP1(X1,k1_xboole_0)
      | sP1(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f65,f104])).

fof(f104,plain,(
    ! [X2] :
      ( k1_xboole_0 = sK5(X2,k1_xboole_0)
      | sP1(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f100,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK5(X0,X1),X1)
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ sP0(X2,X1,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ sP0(sK5(X0,X1),X1,X0)
        & r1_tarski(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f100,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(condensation,[],[f96])).

fof(f96,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_xboole_0)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f79,f92])).

fof(f92,plain,(
    ! [X2,X3] :
      ( r1_tarski(k1_xboole_0,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f75,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK5(X0,X1),X1,X0)
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f261,plain,
    ( sP0(sK4,sK4,sK3)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl8_2
  <=> sP0(sK4,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f268,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f266,f52])).

fof(f52,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f266,plain,
    ( ~ v2_pre_topc(sK3)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f265,f53])).

fof(f265,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f264,f54])).

fof(f264,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | spl8_1 ),
    inference(resolution,[],[f257,f192])).

fof(f192,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f72,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f59,f71])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

fof(f257,plain,
    ( ~ v3_pre_topc(sK4,sK3)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl8_1
  <=> v3_pre_topc(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f262,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f247,f259,f255])).

fof(f247,plain,
    ( sP0(sK4,sK4,sK3)
    | ~ v3_pre_topc(sK4,sK3) ),
    inference(resolution,[],[f235,f55])).

fof(f235,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(X0,X0,X1)
      | ~ v3_pre_topc(X0,X1) ) ),
    inference(condensation,[],[f234])).

fof(f234,plain,(
    ! [X4,X5,X3] :
      ( sP0(X4,X4,X3)
      | ~ v3_pre_topc(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) ) ),
    inference(superposition,[],[f84,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f84,plain,(
    ! [X2,X3,X1] :
      ( sP0(k9_subset_1(u1_struct_0(X2),X1,X3),X1,X2)
      | ~ v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | k9_subset_1(u1_struct_0(X2),X1,X3) != X0
      | ~ v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X2),X1,X3) != X0
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ( k9_subset_1(u1_struct_0(X2),X1,sK6(X0,X1,X2)) = X0
          & v3_pre_topc(sK6(X0,X1,X2),X2)
          & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X2),X1,X4) = X0
          & v3_pre_topc(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( k9_subset_1(u1_struct_0(X2),X1,sK6(X0,X1,X2)) = X0
        & v3_pre_topc(sK6(X0,X1,X2),X2)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X2),X1,X3) != X0
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ? [X4] :
            ( k9_subset_1(u1_struct_0(X2),X1,X4) = X0
            & v3_pre_topc(X4,X2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
            & v3_pre_topc(X3,X0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:13:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.37  ipcrm: permission denied for id (1232928768)
% 0.22/0.38  ipcrm: permission denied for id (1232961545)
% 0.22/0.38  ipcrm: permission denied for id (1232994316)
% 0.22/0.39  ipcrm: permission denied for id (1233027086)
% 0.22/0.39  ipcrm: permission denied for id (1233092625)
% 0.22/0.39  ipcrm: permission denied for id (1233158163)
% 0.22/0.39  ipcrm: permission denied for id (1233190933)
% 0.22/0.40  ipcrm: permission denied for id (1233256470)
% 0.22/0.40  ipcrm: permission denied for id (1233289240)
% 0.22/0.40  ipcrm: permission denied for id (1233354777)
% 0.22/0.40  ipcrm: permission denied for id (1233420316)
% 0.22/0.41  ipcrm: permission denied for id (1233485857)
% 0.22/0.41  ipcrm: permission denied for id (1233518628)
% 0.22/0.43  ipcrm: permission denied for id (1233682478)
% 0.22/0.43  ipcrm: permission denied for id (1233780788)
% 0.22/0.43  ipcrm: permission denied for id (1233813557)
% 0.22/0.44  ipcrm: permission denied for id (1233879097)
% 0.22/0.44  ipcrm: permission denied for id (1233944635)
% 0.22/0.45  ipcrm: permission denied for id (1233977406)
% 0.22/0.46  ipcrm: permission denied for id (1234042954)
% 0.22/0.48  ipcrm: permission denied for id (1234206807)
% 0.22/0.48  ipcrm: permission denied for id (1234337883)
% 0.22/0.49  ipcrm: permission denied for id (1234370656)
% 0.22/0.49  ipcrm: permission denied for id (1234436197)
% 0.22/0.49  ipcrm: permission denied for id (1234468966)
% 0.22/0.51  ipcrm: permission denied for id (1234567279)
% 0.22/0.51  ipcrm: permission denied for id (1234600049)
% 0.22/0.51  ipcrm: permission denied for id (1234731126)
% 0.22/0.52  ipcrm: permission denied for id (1234763896)
% 0.56/0.62  % (20519)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.56/0.64  % (20519)Refutation found. Thanks to Tanya!
% 0.56/0.64  % SZS status Theorem for theBenchmark
% 0.56/0.64  % (20536)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.11/0.65  % (20529)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.11/0.65  % (20533)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.11/0.65  % SZS output start Proof for theBenchmark
% 1.11/0.65  fof(f279,plain,(
% 1.11/0.65    $false),
% 1.11/0.65    inference(avatar_sat_refutation,[],[f262,f268,f278])).
% 1.11/0.65  fof(f278,plain,(
% 1.11/0.65    ~spl8_2),
% 1.11/0.65    inference(avatar_contradiction_clause,[],[f277])).
% 1.11/0.65  fof(f277,plain,(
% 1.11/0.65    $false | ~spl8_2),
% 1.11/0.65    inference(subsumption_resolution,[],[f276,f54])).
% 1.11/0.65  fof(f54,plain,(
% 1.11/0.65    v1_xboole_0(sK4)),
% 1.11/0.65    inference(cnf_transformation,[],[f33])).
% 1.11/0.65  fof(f33,plain,(
% 1.11/0.65    (~v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 1.11/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f17,f32,f31])).
% 1.11/0.65  fof(f31,plain,(
% 1.11/0.65    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.11/0.65    introduced(choice_axiom,[])).
% 1.11/0.65  fof(f32,plain,(
% 1.11/0.65    ? [X1] : (~v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) => (~v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4))),
% 1.11/0.65    introduced(choice_axiom,[])).
% 1.11/0.65  fof(f17,plain,(
% 1.11/0.65    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.11/0.65    inference(flattening,[],[f16])).
% 1.11/0.65  fof(f16,plain,(
% 1.11/0.65    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.11/0.65    inference(ennf_transformation,[],[f15])).
% 1.11/0.65  fof(f15,negated_conjecture,(
% 1.11/0.65    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.11/0.65    inference(negated_conjecture,[],[f14])).
% 1.11/0.65  fof(f14,conjecture,(
% 1.11/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 1.11/0.65  fof(f276,plain,(
% 1.11/0.65    ~v1_xboole_0(sK4) | ~spl8_2),
% 1.11/0.65    inference(subsumption_resolution,[],[f275,f143])).
% 1.11/0.65  fof(f143,plain,(
% 1.11/0.65    ~sP1(sK3,sK4)),
% 1.11/0.65    inference(subsumption_resolution,[],[f141,f56])).
% 1.11/0.65  fof(f56,plain,(
% 1.11/0.65    ~v2_tex_2(sK4,sK3)),
% 1.11/0.65    inference(cnf_transformation,[],[f33])).
% 1.11/0.65  fof(f141,plain,(
% 1.11/0.65    ~sP1(sK3,sK4) | v2_tex_2(sK4,sK3)),
% 1.11/0.65    inference(resolution,[],[f140,f61])).
% 1.11/0.65  fof(f61,plain,(
% 1.11/0.65    ( ! [X0,X1] : (~sP2(X0,X1) | ~sP1(X1,X0) | v2_tex_2(X0,X1)) )),
% 1.11/0.65    inference(cnf_transformation,[],[f35])).
% 1.11/0.65  fof(f35,plain,(
% 1.11/0.65    ! [X0,X1] : (((v2_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v2_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 1.11/0.65    inference(rectify,[],[f34])).
% 1.11/0.65  fof(f34,plain,(
% 1.11/0.65    ! [X1,X0] : (((v2_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v2_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 1.11/0.65    inference(nnf_transformation,[],[f29])).
% 1.11/0.65  fof(f29,plain,(
% 1.11/0.65    ! [X1,X0] : ((v2_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 1.11/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.11/0.65  fof(f140,plain,(
% 1.11/0.65    sP2(sK4,sK3)),
% 1.11/0.65    inference(subsumption_resolution,[],[f137,f53])).
% 1.11/0.65  fof(f53,plain,(
% 1.11/0.65    l1_pre_topc(sK3)),
% 1.11/0.65    inference(cnf_transformation,[],[f33])).
% 1.11/0.65  fof(f137,plain,(
% 1.11/0.65    sP2(sK4,sK3) | ~l1_pre_topc(sK3)),
% 1.11/0.65    inference(resolution,[],[f70,f55])).
% 1.11/0.65  fof(f55,plain,(
% 1.11/0.65    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.11/0.65    inference(cnf_transformation,[],[f33])).
% 1.11/0.65  fof(f70,plain,(
% 1.11/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP2(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.11/0.65    inference(cnf_transformation,[],[f30])).
% 1.11/0.65  fof(f30,plain,(
% 1.11/0.65    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.11/0.65    inference(definition_folding,[],[f19,f29,f28,f27])).
% 1.11/0.65  fof(f27,plain,(
% 1.11/0.65    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> ? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.11/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.11/0.65  fof(f28,plain,(
% 1.11/0.65    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (sP0(X2,X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.11/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.11/0.65  fof(f19,plain,(
% 1.11/0.65    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.11/0.65    inference(flattening,[],[f18])).
% 1.11/0.65  fof(f18,plain,(
% 1.11/0.65    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.11/0.65    inference(ennf_transformation,[],[f13])).
% 1.11/0.65  fof(f13,axiom,(
% 1.11/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).
% 1.11/0.65  fof(f275,plain,(
% 1.11/0.65    sP1(sK3,sK4) | ~v1_xboole_0(sK4) | ~spl8_2),
% 1.11/0.65    inference(resolution,[],[f261,f134])).
% 1.11/0.65  fof(f134,plain,(
% 1.11/0.65    ( ! [X0,X1] : (~sP0(X0,X0,X1) | sP1(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.11/0.65    inference(superposition,[],[f132,f71])).
% 1.11/0.65  fof(f71,plain,(
% 1.11/0.65    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.11/0.65    inference(cnf_transformation,[],[f20])).
% 1.11/0.65  fof(f20,plain,(
% 1.11/0.65    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.11/0.65    inference(ennf_transformation,[],[f3])).
% 1.11/0.65  fof(f3,axiom,(
% 1.11/0.65    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.11/0.65  fof(f132,plain,(
% 1.11/0.65    ( ! [X1] : (~sP0(k1_xboole_0,k1_xboole_0,X1) | sP1(X1,k1_xboole_0)) )),
% 1.11/0.65    inference(duplicate_literal_removal,[],[f129])).
% 1.11/0.65  fof(f129,plain,(
% 1.11/0.65    ( ! [X1] : (~sP0(k1_xboole_0,k1_xboole_0,X1) | sP1(X1,k1_xboole_0) | sP1(X1,k1_xboole_0)) )),
% 1.11/0.65    inference(superposition,[],[f65,f104])).
% 1.11/0.65  fof(f104,plain,(
% 1.11/0.65    ( ! [X2] : (k1_xboole_0 = sK5(X2,k1_xboole_0) | sP1(X2,k1_xboole_0)) )),
% 1.11/0.65    inference(resolution,[],[f100,f64])).
% 1.11/0.65  fof(f64,plain,(
% 1.11/0.65    ( ! [X0,X1] : (r1_tarski(sK5(X0,X1),X1) | sP1(X0,X1)) )),
% 1.11/0.65    inference(cnf_transformation,[],[f39])).
% 1.11/0.65  fof(f39,plain,(
% 1.11/0.65    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(sK5(X0,X1),X1,X0) & r1_tarski(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (sP0(X3,X1,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0,X1)))),
% 1.11/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 1.11/0.65  fof(f38,plain,(
% 1.11/0.65    ! [X1,X0] : (? [X2] : (~sP0(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~sP0(sK5(X0,X1),X1,X0) & r1_tarski(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.11/0.65    introduced(choice_axiom,[])).
% 1.11/0.65  fof(f37,plain,(
% 1.11/0.65    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : (~sP0(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (sP0(X3,X1,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0,X1)))),
% 1.11/0.65    inference(rectify,[],[f36])).
% 1.11/0.65  fof(f36,plain,(
% 1.11/0.65    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : (~sP0(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (sP0(X2,X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0,X1)))),
% 1.11/0.65    inference(nnf_transformation,[],[f28])).
% 1.11/0.65  fof(f100,plain,(
% 1.11/0.65    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.11/0.65    inference(condensation,[],[f96])).
% 1.11/0.65  fof(f96,plain,(
% 1.11/0.65    ( ! [X4,X3] : (k1_xboole_0 = X3 | ~r1_tarski(X3,k1_xboole_0) | ~r1_tarski(X3,X4)) )),
% 1.11/0.65    inference(resolution,[],[f79,f92])).
% 1.11/0.65  fof(f92,plain,(
% 1.11/0.65    ( ! [X2,X3] : (r1_tarski(k1_xboole_0,X2) | ~r1_tarski(X2,X3)) )),
% 1.11/0.65    inference(superposition,[],[f75,f81])).
% 1.11/0.65  fof(f81,plain,(
% 1.11/0.65    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.11/0.65    inference(cnf_transformation,[],[f50])).
% 1.11/0.65  fof(f50,plain,(
% 1.11/0.65    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.11/0.65    inference(nnf_transformation,[],[f5])).
% 1.11/0.65  fof(f5,axiom,(
% 1.11/0.65    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.11/0.65  fof(f75,plain,(
% 1.11/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.11/0.65    inference(cnf_transformation,[],[f6])).
% 1.11/0.65  fof(f6,axiom,(
% 1.11/0.65    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.11/0.65  fof(f79,plain,(
% 1.11/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.11/0.65    inference(cnf_transformation,[],[f49])).
% 1.11/0.65  fof(f49,plain,(
% 1.11/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.11/0.65    inference(flattening,[],[f48])).
% 1.11/0.65  fof(f48,plain,(
% 1.11/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.11/0.65    inference(nnf_transformation,[],[f4])).
% 1.11/0.65  fof(f4,axiom,(
% 1.11/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.11/0.65  fof(f65,plain,(
% 1.11/0.65    ( ! [X0,X1] : (~sP0(sK5(X0,X1),X1,X0) | sP1(X0,X1)) )),
% 1.11/0.65    inference(cnf_transformation,[],[f39])).
% 1.11/0.65  fof(f261,plain,(
% 1.11/0.65    sP0(sK4,sK4,sK3) | ~spl8_2),
% 1.11/0.65    inference(avatar_component_clause,[],[f259])).
% 1.11/0.65  fof(f259,plain,(
% 1.11/0.65    spl8_2 <=> sP0(sK4,sK4,sK3)),
% 1.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.11/0.65  fof(f268,plain,(
% 1.11/0.65    spl8_1),
% 1.11/0.65    inference(avatar_contradiction_clause,[],[f267])).
% 1.11/0.65  fof(f267,plain,(
% 1.11/0.65    $false | spl8_1),
% 1.11/0.65    inference(subsumption_resolution,[],[f266,f52])).
% 1.11/0.65  fof(f52,plain,(
% 1.11/0.65    v2_pre_topc(sK3)),
% 1.11/0.65    inference(cnf_transformation,[],[f33])).
% 1.11/0.65  fof(f266,plain,(
% 1.11/0.65    ~v2_pre_topc(sK3) | spl8_1),
% 1.11/0.65    inference(subsumption_resolution,[],[f265,f53])).
% 1.11/0.65  fof(f265,plain,(
% 1.11/0.65    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | spl8_1),
% 1.11/0.65    inference(subsumption_resolution,[],[f264,f54])).
% 1.11/0.65  fof(f264,plain,(
% 1.11/0.65    ~v1_xboole_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | spl8_1),
% 1.11/0.65    inference(resolution,[],[f257,f192])).
% 1.11/0.65  fof(f192,plain,(
% 1.11/0.65    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.11/0.65    inference(subsumption_resolution,[],[f72,f88])).
% 1.11/0.65  fof(f88,plain,(
% 1.11/0.65    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X0)) )),
% 1.11/0.65    inference(superposition,[],[f59,f71])).
% 1.11/0.65  fof(f59,plain,(
% 1.11/0.65    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.11/0.65    inference(cnf_transformation,[],[f9])).
% 1.11/0.65  fof(f9,axiom,(
% 1.11/0.65    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.11/0.65  fof(f72,plain,(
% 1.11/0.65    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.11/0.65    inference(cnf_transformation,[],[f22])).
% 1.11/0.65  fof(f22,plain,(
% 1.11/0.65    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.11/0.65    inference(flattening,[],[f21])).
% 1.11/0.65  fof(f21,plain,(
% 1.11/0.65    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.11/0.65    inference(ennf_transformation,[],[f12])).
% 1.11/0.65  fof(f12,axiom,(
% 1.11/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 1.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).
% 1.11/0.65  fof(f257,plain,(
% 1.11/0.65    ~v3_pre_topc(sK4,sK3) | spl8_1),
% 1.11/0.65    inference(avatar_component_clause,[],[f255])).
% 1.11/0.65  fof(f255,plain,(
% 1.11/0.65    spl8_1 <=> v3_pre_topc(sK4,sK3)),
% 1.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.11/0.65  fof(f262,plain,(
% 1.11/0.65    ~spl8_1 | spl8_2),
% 1.11/0.65    inference(avatar_split_clause,[],[f247,f259,f255])).
% 1.11/0.65  fof(f247,plain,(
% 1.11/0.65    sP0(sK4,sK4,sK3) | ~v3_pre_topc(sK4,sK3)),
% 1.11/0.65    inference(resolution,[],[f235,f55])).
% 1.11/0.65  fof(f235,plain,(
% 1.11/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | sP0(X0,X0,X1) | ~v3_pre_topc(X0,X1)) )),
% 1.11/0.65    inference(condensation,[],[f234])).
% 1.11/0.65  fof(f234,plain,(
% 1.11/0.65    ( ! [X4,X5,X3] : (sP0(X4,X4,X3) | ~v3_pre_topc(X4,X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) )),
% 1.11/0.65    inference(superposition,[],[f84,f82])).
% 1.11/0.65  fof(f82,plain,(
% 1.11/0.65    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.11/0.65    inference(cnf_transformation,[],[f24])).
% 1.11/0.65  fof(f24,plain,(
% 1.11/0.65    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.11/0.65    inference(ennf_transformation,[],[f8])).
% 1.11/0.65  fof(f8,axiom,(
% 1.11/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 1.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 1.11/0.65  fof(f84,plain,(
% 1.11/0.65    ( ! [X2,X3,X1] : (sP0(k9_subset_1(u1_struct_0(X2),X1,X3),X1,X2) | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.11/0.65    inference(equality_resolution,[],[f69])).
% 1.11/0.65  fof(f69,plain,(
% 1.11/0.65    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | k9_subset_1(u1_struct_0(X2),X1,X3) != X0 | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.11/0.65    inference(cnf_transformation,[],[f43])).
% 1.11/0.65  fof(f43,plain,(
% 1.11/0.65    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (k9_subset_1(u1_struct_0(X2),X1,X3) != X0 | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & ((k9_subset_1(u1_struct_0(X2),X1,sK6(X0,X1,X2)) = X0 & v3_pre_topc(sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 1.11/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f42])).
% 1.11/0.65  fof(f42,plain,(
% 1.11/0.65    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X2),X1,X4) = X0 & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) => (k9_subset_1(u1_struct_0(X2),X1,sK6(X0,X1,X2)) = X0 & v3_pre_topc(sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 1.11/0.65    introduced(choice_axiom,[])).
% 1.11/0.65  fof(f41,plain,(
% 1.11/0.65    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (k9_subset_1(u1_struct_0(X2),X1,X3) != X0 | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (? [X4] : (k9_subset_1(u1_struct_0(X2),X1,X4) = X0 & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 1.11/0.65    inference(rectify,[],[f40])).
% 1.11/0.65  fof(f40,plain,(
% 1.11/0.65    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | ! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X2,X1,X0)))),
% 1.11/0.65    inference(nnf_transformation,[],[f27])).
% 1.11/0.65  % SZS output end Proof for theBenchmark
% 1.11/0.65  % (20519)------------------------------
% 1.11/0.65  % (20519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.11/0.65  % (20519)Termination reason: Refutation
% 1.11/0.65  
% 1.11/0.65  % (20519)Memory used [KB]: 6268
% 1.11/0.65  % (20519)Time elapsed: 0.063 s
% 1.11/0.65  % (20519)------------------------------
% 1.11/0.65  % (20519)------------------------------
% 1.11/0.66  % (20378)Success in time 0.292 s
%------------------------------------------------------------------------------
