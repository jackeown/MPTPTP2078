%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 276 expanded)
%              Number of leaves         :   20 (  84 expanded)
%              Depth                    :   17
%              Number of atoms          :  303 (1141 expanded)
%              Number of equality atoms :   99 ( 308 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f457,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f206,f339,f406,f419,f456])).

fof(f456,plain,
    ( ~ spl4_2
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f454,f126])).

fof(f126,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f47,f115])).

fof(f115,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f47,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK0 != sK1
    & r1_tarski(sK0,sK1)
    & v1_zfmisc_1(sK1)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r1_tarski(sK0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r1_tarski(sK0,X1)
        & v1_zfmisc_1(X1)
        & ~ v1_xboole_0(X1) )
   => ( sK0 != sK1
      & r1_tarski(sK0,sK1)
      & v1_zfmisc_1(sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f454,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f453,f52])).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f453,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0)
    | ~ spl4_12 ),
    inference(resolution,[],[f445,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f445,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_12 ),
    inference(trivial_inequality_removal,[],[f444])).

fof(f444,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_12 ),
    inference(superposition,[],[f63,f348])).

fof(f348,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f346])).

fof(f346,plain,
    ( spl4_12
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f419,plain,
    ( ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(resolution,[],[f338,f124])).

fof(f124,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f92,f115])).

fof(f92,plain,(
    ~ r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f90,f51])).

fof(f51,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f50,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f50,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f338,plain,
    ( ! [X1] : r1_tarski(sK1,X1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl4_10
  <=> ! [X1] : r1_tarski(sK1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f406,plain,
    ( ~ spl4_9
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f405])).

fof(f405,plain,
    ( $false
    | ~ spl4_9
    | spl4_12 ),
    inference(trivial_inequality_removal,[],[f404])).

fof(f404,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_9
    | spl4_12 ),
    inference(superposition,[],[f347,f335])).

fof(f335,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl4_9
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f347,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f346])).

fof(f339,plain,
    ( spl4_9
    | spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f332,f113,f337,f334])).

fof(f332,plain,
    ( ! [X0,X1] :
        ( r1_tarski(sK1,X1)
        | k1_xboole_0 = k4_xboole_0(X0,X0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f323,f56])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f323,plain,
    ( ! [X0,X1] :
        ( r1_tarski(sK1,X1)
        | ~ r1_tarski(X0,k2_xboole_0(X0,X1))
        | k1_xboole_0 = k4_xboole_0(X0,X0) )
    | ~ spl4_2 ),
    inference(superposition,[],[f69,f195])).

fof(f195,plain,
    ( ! [X21] :
        ( sK1 = k4_xboole_0(X21,X21)
        | k1_xboole_0 = k4_xboole_0(X21,X21) )
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f192])).

fof(f192,plain,
    ( ! [X21] :
        ( sK1 != sK1
        | k1_xboole_0 = k4_xboole_0(X21,X21)
        | sK1 = k4_xboole_0(X21,X21) )
    | ~ spl4_2 ),
    inference(superposition,[],[f148,f174])).

fof(f174,plain,
    ( ! [X0] : sK1 = k2_xboole_0(k4_xboole_0(X0,X0),sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f155,f56])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0))
        | sK1 = k2_xboole_0(k4_xboole_0(X0,X1),sK1) )
    | ~ spl4_2 ),
    inference(resolution,[],[f151,f69])).

fof(f151,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,k1_xboole_0)
        | sK1 = k2_xboole_0(X3,sK1) )
    | ~ spl4_2 ),
    inference(resolution,[],[f125,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f125,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f89,f115])).

fof(f89,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK1)
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f50,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f148,plain,(
    ! [X14,X15] :
      ( sK1 != k2_xboole_0(X14,X15)
      | k1_xboole_0 = X14
      | sK1 = X14 ) ),
    inference(superposition,[],[f84,f95])).

fof(f95,plain,(
    sK1 = k1_tarski(sK2(sK1)) ),
    inference(forward_demodulation,[],[f94,f88])).

fof(f88,plain,(
    sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    inference(subsumption_resolution,[],[f86,f48])).

fof(f48,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f49,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

% (1057)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f40,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f49,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f94,plain,(
    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) ),
    inference(subsumption_resolution,[],[f93,f48])).

fof(f93,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f87,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f87,plain,(
    m1_subset_1(sK2(sK1),sK1) ),
    inference(subsumption_resolution,[],[f85,f48])).

fof(f85,plain,
    ( m1_subset_1(sK2(sK1),sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f49,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) != k1_tarski(X0)
      | k1_xboole_0 = X1
      | k1_tarski(X0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = X1
      | k1_xboole_0 = X1
      | k1_tarski(X0) = X1
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f206,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f204])).

fof(f204,plain,
    ( sK1 != sK1
    | ~ spl4_3 ),
    inference(superposition,[],[f118,f95])).

fof(f118,plain,
    ( ! [X2] : sK1 != k1_tarski(X2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_3
  <=> ! [X2] : sK1 != k1_tarski(X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f122,plain,
    ( spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f121,f117,f113])).

fof(f121,plain,(
    ! [X8] :
      ( sK1 != k1_tarski(X8)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f120,f51])).

fof(f120,plain,(
    ! [X8] :
      ( sK1 != k1_tarski(X8)
      | k1_xboole_0 = sK0
      | sK0 = sK1 ) ),
    inference(inner_rewriting,[],[f105])).

fof(f105,plain,(
    ! [X8] :
      ( sK1 != k1_tarski(X8)
      | k1_xboole_0 = sK0
      | sK0 = k1_tarski(X8) ) ),
    inference(superposition,[],[f84,f91])).

fof(f91,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f50,f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:27:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (1041)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (1032)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (1059)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (1037)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (1067)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (1039)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (1042)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (1066)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (1062)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (1034)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (1069)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (1058)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (1036)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (1075)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (1061)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (1060)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (1064)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (1064)Refutation not found, incomplete strategy% (1064)------------------------------
% 0.21/0.53  % (1064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1064)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1064)Memory used [KB]: 10618
% 0.21/0.53  % (1064)Time elapsed: 0.119 s
% 0.21/0.53  % (1064)------------------------------
% 0.21/0.53  % (1064)------------------------------
% 0.21/0.53  % (1076)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (1070)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (1074)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (1033)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (1073)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (1065)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (1040)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (1072)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (1055)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (1068)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (1042)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f457,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f122,f206,f339,f406,f419,f456])).
% 0.21/0.54  fof(f456,plain,(
% 0.21/0.54    ~spl4_2 | ~spl4_12),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f455])).
% 0.21/0.54  fof(f455,plain,(
% 0.21/0.54    $false | (~spl4_2 | ~spl4_12)),
% 0.21/0.54    inference(subsumption_resolution,[],[f454,f126])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    ~v1_xboole_0(k1_xboole_0) | ~spl4_2),
% 0.21/0.54    inference(backward_demodulation,[],[f47,f115])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    k1_xboole_0 = sK0 | ~spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f113])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    spl4_2 <=> k1_xboole_0 = sK0),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ~v1_xboole_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f35,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.54    inference(negated_conjecture,[],[f15])).
% 0.21/0.54  fof(f15,conjecture,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.54  fof(f454,plain,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0) | ~spl4_12),
% 0.21/0.54    inference(subsumption_resolution,[],[f453,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f453,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,k1_xboole_0) | v1_xboole_0(k1_xboole_0) | ~spl4_12),
% 0.21/0.54    inference(resolution,[],[f445,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.21/0.54    inference(flattening,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.54  fof(f445,plain,(
% 0.21/0.54    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_12),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f444])).
% 0.21/0.54  fof(f444,plain,(
% 0.21/0.54    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_12),
% 0.21/0.54    inference(superposition,[],[f63,f348])).
% 0.21/0.54  fof(f348,plain,(
% 0.21/0.54    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f346])).
% 0.21/0.54  fof(f346,plain,(
% 0.21/0.54    spl4_12 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 0.21/0.54    inference(unused_predicate_definition_removal,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.54  fof(f419,plain,(
% 0.21/0.54    ~spl4_2 | ~spl4_10),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f407])).
% 0.21/0.54  fof(f407,plain,(
% 0.21/0.54    $false | (~spl4_2 | ~spl4_10)),
% 0.21/0.54    inference(resolution,[],[f338,f124])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    ~r1_tarski(sK1,k1_xboole_0) | ~spl4_2),
% 0.21/0.54    inference(backward_demodulation,[],[f92,f115])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ~r1_tarski(sK1,sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f90,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    sK0 != sK1),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    sK0 = sK1 | ~r1_tarski(sK1,sK0)),
% 0.21/0.54    inference(resolution,[],[f50,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f338,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(sK1,X1)) ) | ~spl4_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f337])).
% 0.21/0.54  fof(f337,plain,(
% 0.21/0.54    spl4_10 <=> ! [X1] : r1_tarski(sK1,X1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.54  fof(f406,plain,(
% 0.21/0.54    ~spl4_9 | spl4_12),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f405])).
% 0.21/0.54  fof(f405,plain,(
% 0.21/0.54    $false | (~spl4_9 | spl4_12)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f404])).
% 0.21/0.54  fof(f404,plain,(
% 0.21/0.54    k1_xboole_0 != k1_xboole_0 | (~spl4_9 | spl4_12)),
% 0.21/0.54    inference(superposition,[],[f347,f335])).
% 0.21/0.54  fof(f335,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl4_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f334])).
% 0.21/0.54  fof(f334,plain,(
% 0.21/0.54    spl4_9 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.54  fof(f347,plain,(
% 0.21/0.54    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | spl4_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f346])).
% 0.21/0.54  fof(f339,plain,(
% 0.21/0.54    spl4_9 | spl4_10 | ~spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f332,f113,f337,f334])).
% 0.21/0.54  fof(f332,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(sK1,X1) | k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl4_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f323,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.54  fof(f323,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(sK1,X1) | ~r1_tarski(X0,k2_xboole_0(X0,X1)) | k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl4_2),
% 0.21/0.54    inference(superposition,[],[f69,f195])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    ( ! [X21] : (sK1 = k4_xboole_0(X21,X21) | k1_xboole_0 = k4_xboole_0(X21,X21)) ) | ~spl4_2),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f192])).
% 0.21/0.54  fof(f192,plain,(
% 0.21/0.54    ( ! [X21] : (sK1 != sK1 | k1_xboole_0 = k4_xboole_0(X21,X21) | sK1 = k4_xboole_0(X21,X21)) ) | ~spl4_2),
% 0.21/0.54    inference(superposition,[],[f148,f174])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    ( ! [X0] : (sK1 = k2_xboole_0(k4_xboole_0(X0,X0),sK1)) ) | ~spl4_2),
% 0.21/0.54    inference(resolution,[],[f155,f56])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0)) | sK1 = k2_xboole_0(k4_xboole_0(X0,X1),sK1)) ) | ~spl4_2),
% 0.21/0.54    inference(resolution,[],[f151,f69])).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | sK1 = k2_xboole_0(X3,sK1)) ) | ~spl4_2),
% 0.21/0.54    inference(resolution,[],[f125,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(X0,sK1) | ~r1_tarski(X0,k1_xboole_0)) ) | ~spl4_2),
% 0.21/0.54    inference(backward_demodulation,[],[f89,f115])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(X0,sK1) | ~r1_tarski(X0,sK0)) )),
% 0.21/0.54    inference(resolution,[],[f50,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    ( ! [X14,X15] : (sK1 != k2_xboole_0(X14,X15) | k1_xboole_0 = X14 | sK1 = X14) )),
% 0.21/0.54    inference(superposition,[],[f84,f95])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    sK1 = k1_tarski(sK2(sK1))),
% 0.21/0.54    inference(forward_demodulation,[],[f94,f88])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    sK1 = k6_domain_1(sK1,sK2(sK1))),
% 0.21/0.54    inference(subsumption_resolution,[],[f86,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ~v1_xboole_0(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    sK1 = k6_domain_1(sK1,sK2(sK1)) | v1_xboole_0(sK1)),
% 0.21/0.54    inference(resolution,[],[f49,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_zfmisc_1(X0) | k6_domain_1(X0,sK2(X0)) = X0 | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  % (1057)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.54    inference(rectify,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    v1_zfmisc_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))),
% 0.21/0.54    inference(subsumption_resolution,[],[f93,f48])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | v1_xboole_0(sK1)),
% 0.21/0.54    inference(resolution,[],[f87,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    m1_subset_1(sK2(sK1),sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f85,f48])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    m1_subset_1(sK2(sK1),sK1) | v1_xboole_0(sK1)),
% 0.21/0.54    inference(resolution,[],[f49,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_zfmisc_1(X0) | m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) != k1_tarski(X0) | k1_xboole_0 = X1 | k1_tarski(X0) = X1) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_tarski(X0) = X1 | k1_xboole_0 = X1 | k1_tarski(X0) = X1 | k2_xboole_0(X1,X2) != k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k1_xboole_0 = X2 & k1_tarski(X0) = X1) | (k1_tarski(X0) = X2 & k1_xboole_0 = X1) | (k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | k2_xboole_0(X1,X2) != k1_tarski(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.21/0.54  fof(f206,plain,(
% 0.21/0.54    ~spl4_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f205])).
% 0.21/0.54  fof(f205,plain,(
% 0.21/0.54    $false | ~spl4_3),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f204])).
% 0.21/0.54  fof(f204,plain,(
% 0.21/0.54    sK1 != sK1 | ~spl4_3),
% 0.21/0.54    inference(superposition,[],[f118,f95])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    ( ! [X2] : (sK1 != k1_tarski(X2)) ) | ~spl4_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f117])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    spl4_3 <=> ! [X2] : sK1 != k1_tarski(X2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    spl4_2 | spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f121,f117,f113])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    ( ! [X8] : (sK1 != k1_tarski(X8) | k1_xboole_0 = sK0) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f120,f51])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    ( ! [X8] : (sK1 != k1_tarski(X8) | k1_xboole_0 = sK0 | sK0 = sK1) )),
% 0.21/0.54    inference(inner_rewriting,[],[f105])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    ( ! [X8] : (sK1 != k1_tarski(X8) | k1_xboole_0 = sK0 | sK0 = k1_tarski(X8)) )),
% 0.21/0.54    inference(superposition,[],[f84,f91])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    sK1 = k2_xboole_0(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f50,f58])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (1042)------------------------------
% 0.21/0.54  % (1042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1042)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (1042)Memory used [KB]: 10874
% 0.21/0.54  % (1042)Time elapsed: 0.138 s
% 0.21/0.54  % (1042)------------------------------
% 0.21/0.54  % (1042)------------------------------
% 0.21/0.54  % (1031)Success in time 0.187 s
%------------------------------------------------------------------------------
