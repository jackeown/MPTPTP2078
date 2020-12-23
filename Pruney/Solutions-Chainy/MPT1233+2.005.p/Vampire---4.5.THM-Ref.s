%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 171 expanded)
%              Number of leaves         :   23 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  290 ( 461 expanded)
%              Number of equality atoms :   58 ( 110 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f322,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f174,f256,f286,f301,f305,f311,f313,f321])).

fof(f321,plain,(
    spl1_5 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | spl1_5 ),
    inference(subsumption_resolution,[],[f319,f39])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f319,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl1_5 ),
    inference(subsumption_resolution,[],[f316,f40])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f316,plain,
    ( u1_struct_0(sK0) != k4_xboole_0(u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl1_5 ),
    inference(superposition,[],[f169,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

% (6717)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f169,plain,
    ( u1_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl1_5
  <=> u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f313,plain,
    ( ~ spl1_5
    | spl1_8
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f312,f294,f253,f167])).

fof(f253,plain,
    ( spl1_8
  <=> k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f294,plain,
    ( spl1_10
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f312,plain,
    ( u1_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | spl1_8
    | ~ spl1_10 ),
    inference(forward_demodulation,[],[f255,f296])).

fof(f296,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f294])).

fof(f255,plain,
    ( k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | spl1_8 ),
    inference(avatar_component_clause,[],[f253])).

fof(f311,plain,
    ( spl1_7
    | ~ spl1_10 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | spl1_7
    | ~ spl1_10 ),
    inference(subsumption_resolution,[],[f309,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f41,f38])).

fof(f38,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f309,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl1_7
    | ~ spl1_10 ),
    inference(forward_demodulation,[],[f251,f296])).

fof(f251,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl1_7 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl1_7
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f305,plain,
    ( spl1_10
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f304,f290,f245,f294])).

fof(f245,plain,
    ( spl1_6
  <=> r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f290,plain,
    ( spl1_9
  <=> r1_tarski(k2_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f304,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f302,f246])).

fof(f246,plain,
    ( r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f245])).

fof(f302,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl1_9 ),
    inference(resolution,[],[f291,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f291,plain,
    ( r1_tarski(k2_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f290])).

fof(f301,plain,
    ( ~ spl1_1
    | spl1_9 ),
    inference(avatar_contradiction_clause,[],[f300])).

% (6709)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f300,plain,
    ( $false
    | ~ spl1_1
    | spl1_9 ),
    inference(subsumption_resolution,[],[f299,f61])).

fof(f61,plain,
    ( l1_struct_0(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl1_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f299,plain,
    ( ~ l1_struct_0(sK0)
    | spl1_9 ),
    inference(subsumption_resolution,[],[f298,f55])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f298,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | spl1_9 ),
    inference(superposition,[],[f292,f42])).

fof(f42,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f292,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),u1_struct_0(sK0))
    | spl1_9 ),
    inference(avatar_component_clause,[],[f290])).

fof(f286,plain,
    ( ~ spl1_1
    | spl1_6 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | ~ spl1_1
    | spl1_6 ),
    inference(subsumption_resolution,[],[f284,f61])).

fof(f284,plain,
    ( ~ l1_struct_0(sK0)
    | spl1_6 ),
    inference(subsumption_resolution,[],[f283,f55])).

fof(f283,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | spl1_6 ),
    inference(superposition,[],[f247,f42])).

fof(f247,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0))
    | spl1_6 ),
    inference(avatar_component_clause,[],[f245])).

fof(f256,plain,
    ( ~ spl1_6
    | ~ spl1_7
    | ~ spl1_8
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f243,f159,f253,f249,f245])).

fof(f159,plain,
    ( spl1_3
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f243,plain,
    ( k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f242,f160])).

fof(f160,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f159])).

fof(f242,plain,
    ( k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ v4_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f224,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

fof(f224,plain,
    ( k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ v4_pre_topc(k1_xboole_0,sK0) ),
    inference(superposition,[],[f36,f211])).

fof(f211,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k1_xboole_0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(u1_struct_0(X0),X1)
      | ~ v4_pre_topc(k1_xboole_0,X0) ) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k1_xboole_0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(u1_struct_0(X0),X1)
      | ~ v4_pre_topc(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f97,f84])).

fof(f84,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_pre_topc(X0,k1_xboole_0)
      | ~ v4_pre_topc(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f45,f39])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f97,plain,(
    ! [X2,X1] :
      ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k1_xboole_0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ r1_tarski(u1_struct_0(X1),X2) ) ),
    inference(superposition,[],[f94,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

% (6709)Refutation not found, incomplete strategy% (6709)------------------------------
% (6709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6709)Termination reason: Refutation not found, incomplete strategy

% (6709)Memory used [KB]: 6140
% (6709)Time elapsed: 0.092 s
% (6709)------------------------------
% (6709)------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f94,plain,(
    ! [X2,X3] :
      ( k1_tops_1(X2,X3) = k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,k4_xboole_0(u1_struct_0(X2),X3)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X2,X3] :
      ( k1_tops_1(X2,X3) = k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,k4_xboole_0(u1_struct_0(X2),X3)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f44,f48])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f36,plain,(
    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f174,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl1_3 ),
    inference(subsumption_resolution,[],[f172,f34])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f172,plain,
    ( ~ v2_pre_topc(sK0)
    | spl1_3 ),
    inference(subsumption_resolution,[],[f171,f35])).

fof(f171,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl1_3 ),
    inference(resolution,[],[f161,f83])).

fof(f83,plain,(
    ! [X0] :
      ( v4_pre_topc(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f81,f37])).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v4_pre_topc(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f47,f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f161,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | spl1_3 ),
    inference(avatar_component_clause,[],[f159])).

fof(f70,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl1_1 ),
    inference(subsumption_resolution,[],[f68,f35])).

fof(f68,plain,
    ( ~ l1_pre_topc(sK0)
    | spl1_1 ),
    inference(resolution,[],[f62,f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f62,plain,
    ( ~ l1_struct_0(sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (6708)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (6710)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (6708)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (6706)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (6710)Refutation not found, incomplete strategy% (6710)------------------------------
% 0.20/0.50  % (6710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (6710)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (6710)Memory used [KB]: 10490
% 0.20/0.50  % (6710)Time elapsed: 0.082 s
% 0.20/0.50  % (6710)------------------------------
% 0.20/0.50  % (6710)------------------------------
% 0.20/0.50  % (6716)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (6725)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f322,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f70,f174,f256,f286,f301,f305,f311,f313,f321])).
% 0.20/0.50  fof(f321,plain,(
% 0.20/0.50    spl1_5),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f320])).
% 0.20/0.50  fof(f320,plain,(
% 0.20/0.50    $false | spl1_5),
% 0.20/0.50    inference(subsumption_resolution,[],[f319,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.50  fof(f319,plain,(
% 0.20/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | spl1_5),
% 0.20/0.50    inference(subsumption_resolution,[],[f316,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.50  fof(f316,plain,(
% 0.20/0.50    u1_struct_0(sK0) != k4_xboole_0(u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | spl1_5),
% 0.20/0.50    inference(superposition,[],[f169,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  % (6717)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    u1_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | spl1_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f167])).
% 0.20/0.50  fof(f167,plain,(
% 0.20/0.50    spl1_5 <=> u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.50  fof(f313,plain,(
% 0.20/0.50    ~spl1_5 | spl1_8 | ~spl1_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f312,f294,f253,f167])).
% 0.20/0.50  fof(f253,plain,(
% 0.20/0.50    spl1_8 <=> k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.20/0.50  fof(f294,plain,(
% 0.20/0.50    spl1_10 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.20/0.50  fof(f312,plain,(
% 0.20/0.50    u1_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | (spl1_8 | ~spl1_10)),
% 0.20/0.50    inference(forward_demodulation,[],[f255,f296])).
% 0.20/0.50  fof(f296,plain,(
% 0.20/0.50    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl1_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f294])).
% 0.20/0.50  fof(f255,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | spl1_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f253])).
% 0.20/0.50  fof(f311,plain,(
% 0.20/0.50    spl1_7 | ~spl1_10),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f310])).
% 0.20/0.50  fof(f310,plain,(
% 0.20/0.50    $false | (spl1_7 | ~spl1_10)),
% 0.20/0.50    inference(subsumption_resolution,[],[f309,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f41,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.50  fof(f309,plain,(
% 0.20/0.50    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (spl1_7 | ~spl1_10)),
% 0.20/0.50    inference(forward_demodulation,[],[f251,f296])).
% 0.20/0.50  fof(f251,plain,(
% 0.20/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl1_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f249])).
% 0.20/0.50  fof(f249,plain,(
% 0.20/0.50    spl1_7 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.20/0.50  fof(f305,plain,(
% 0.20/0.50    spl1_10 | ~spl1_6 | ~spl1_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f304,f290,f245,f294])).
% 0.20/0.50  fof(f245,plain,(
% 0.20/0.50    spl1_6 <=> r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.50  fof(f290,plain,(
% 0.20/0.50    spl1_9 <=> r1_tarski(k2_struct_0(sK0),u1_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.20/0.50  fof(f304,plain,(
% 0.20/0.50    k2_struct_0(sK0) = u1_struct_0(sK0) | (~spl1_6 | ~spl1_9)),
% 0.20/0.50    inference(subsumption_resolution,[],[f302,f246])).
% 0.20/0.50  fof(f246,plain,(
% 0.20/0.50    r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0)) | ~spl1_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f245])).
% 0.20/0.50  fof(f302,plain,(
% 0.20/0.50    k2_struct_0(sK0) = u1_struct_0(sK0) | ~r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0)) | ~spl1_9),
% 0.20/0.50    inference(resolution,[],[f291,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(flattening,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f291,plain,(
% 0.20/0.50    r1_tarski(k2_struct_0(sK0),u1_struct_0(sK0)) | ~spl1_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f290])).
% 0.20/0.50  fof(f301,plain,(
% 0.20/0.50    ~spl1_1 | spl1_9),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f300])).
% 0.20/0.50  % (6709)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  fof(f300,plain,(
% 0.20/0.50    $false | (~spl1_1 | spl1_9)),
% 0.20/0.50    inference(subsumption_resolution,[],[f299,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    l1_struct_0(sK0) | ~spl1_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    spl1_1 <=> l1_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.50  fof(f299,plain,(
% 0.20/0.50    ~l1_struct_0(sK0) | spl1_9),
% 0.20/0.50    inference(subsumption_resolution,[],[f298,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f298,plain,(
% 0.20/0.50    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | ~l1_struct_0(sK0) | spl1_9),
% 0.20/0.50    inference(superposition,[],[f292,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.50  fof(f292,plain,(
% 0.20/0.50    ~r1_tarski(k2_struct_0(sK0),u1_struct_0(sK0)) | spl1_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f290])).
% 0.20/0.50  fof(f286,plain,(
% 0.20/0.50    ~spl1_1 | spl1_6),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f285])).
% 0.20/0.50  fof(f285,plain,(
% 0.20/0.50    $false | (~spl1_1 | spl1_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f284,f61])).
% 0.20/0.50  fof(f284,plain,(
% 0.20/0.50    ~l1_struct_0(sK0) | spl1_6),
% 0.20/0.50    inference(subsumption_resolution,[],[f283,f55])).
% 0.20/0.50  fof(f283,plain,(
% 0.20/0.50    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | ~l1_struct_0(sK0) | spl1_6),
% 0.20/0.50    inference(superposition,[],[f247,f42])).
% 0.20/0.50  fof(f247,plain,(
% 0.20/0.50    ~r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0)) | spl1_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f245])).
% 0.20/0.50  fof(f256,plain,(
% 0.20/0.50    ~spl1_6 | ~spl1_7 | ~spl1_8 | ~spl1_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f243,f159,f253,f249,f245])).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    spl1_3 <=> v4_pre_topc(k1_xboole_0,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.50  fof(f243,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0)) | ~spl1_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f242,f160])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    v4_pre_topc(k1_xboole_0,sK0) | ~spl1_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f159])).
% 0.20/0.50  fof(f242,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0)) | ~v4_pre_topc(k1_xboole_0,sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f224,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.20/0.50    inference(negated_conjecture,[],[f15])).
% 0.20/0.50  fof(f15,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).
% 0.20/0.50  fof(f224,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0)) | ~v4_pre_topc(k1_xboole_0,sK0)),
% 0.20/0.50    inference(superposition,[],[f36,f211])).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(u1_struct_0(X0),X1) | ~v4_pre_topc(k1_xboole_0,X0)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f194])).
% 0.20/0.50  fof(f194,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(u1_struct_0(X0),X1) | ~v4_pre_topc(k1_xboole_0,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(superposition,[],[f97,f84])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k2_pre_topc(X0,k1_xboole_0) | ~v4_pre_topc(k1_xboole_0,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(resolution,[],[f45,f39])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    ( ! [X2,X1] : (k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k1_xboole_0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~r1_tarski(u1_struct_0(X1),X2)) )),
% 0.20/0.50    inference(superposition,[],[f94,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f3])).
% 0.20/0.50  % (6709)Refutation not found, incomplete strategy% (6709)------------------------------
% 0.20/0.50  % (6709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (6709)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (6709)Memory used [KB]: 6140
% 0.20/0.50  % (6709)Time elapsed: 0.092 s
% 0.20/0.50  % (6709)------------------------------
% 0.20/0.50  % (6709)------------------------------
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k1_tops_1(X2,X3) = k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,k4_xboole_0(u1_struct_0(X2),X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f91])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k1_tops_1(X2,X3) = k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,k4_xboole_0(u1_struct_0(X2),X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.20/0.50    inference(superposition,[],[f44,f48])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f174,plain,(
% 0.20/0.50    spl1_3),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f173])).
% 0.20/0.50  fof(f173,plain,(
% 0.20/0.50    $false | spl1_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f172,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    v2_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | spl1_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f171,f35])).
% 0.20/0.50  fof(f171,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl1_3),
% 0.20/0.50    inference(resolution,[],[f161,f83])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X0] : (v4_pre_topc(k1_xboole_0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f81,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | v4_pre_topc(k1_xboole_0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.50    inference(resolution,[],[f47,f39])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    ~v4_pre_topc(k1_xboole_0,sK0) | spl1_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f159])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    spl1_1),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    $false | spl1_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f68,f35])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | spl1_1),
% 0.20/0.50    inference(resolution,[],[f62,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ~l1_struct_0(sK0) | spl1_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f60])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (6708)------------------------------
% 0.20/0.50  % (6708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (6708)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (6708)Memory used [KB]: 6268
% 0.20/0.50  % (6708)Time elapsed: 0.074 s
% 0.20/0.50  % (6708)------------------------------
% 0.20/0.50  % (6708)------------------------------
% 0.20/0.51  % (6695)Success in time 0.147 s
%------------------------------------------------------------------------------
