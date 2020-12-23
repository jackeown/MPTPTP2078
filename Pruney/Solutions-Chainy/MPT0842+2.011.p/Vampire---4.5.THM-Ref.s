%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 156 expanded)
%              Number of leaves         :   19 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  256 ( 577 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f48,f57,f69,f74,f128,f148,f180,f193,f211,f227,f231])).

fof(f231,plain,
    ( ~ spl7_8
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f228,f225,f46,f42,f72])).

fof(f72,plain,
    ( spl7_8
  <=> r2_hidden(sK5,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f42,plain,
    ( spl7_2
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f46,plain,
    ( spl7_3
  <=> r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f225,plain,
    ( spl7_24
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(k4_tarski(sK4,X0),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f228,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ r2_hidden(sK5,k2_relat_1(sK3))
    | ~ spl7_3
    | ~ spl7_24 ),
    inference(resolution,[],[f226,f47])).

fof(f47,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK4,X0),sK3)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK3)) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f225])).

fof(f227,plain,
    ( ~ spl7_7
    | spl7_24
    | spl7_1 ),
    inference(avatar_split_clause,[],[f223,f39,f225,f65])).

fof(f65,plain,
    ( spl7_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f39,plain,
    ( spl7_1
  <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | ~ r2_hidden(k4_tarski(sK4,X0),sK3)
        | ~ r2_hidden(X0,sK1)
        | ~ v1_relat_1(sK3) )
    | spl7_1 ),
    inference(resolution,[],[f212,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f212,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | spl7_1 ),
    inference(forward_demodulation,[],[f53,f132])).

fof(f132,plain,(
    ! [X10] : k8_relset_1(sK0,sK2,sK3,X10) = k10_relat_1(sK3,X10) ),
    inference(resolution,[],[f37,f26])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

% (29485)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% (29501)Termination reason: Refutation not found, incomplete strategy

% (29501)Memory used [KB]: 10618
% (29501)Time elapsed: 0.059 s
% (29501)------------------------------
% (29501)------------------------------
% (29494)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% (29498)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X4,X5),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f53,plain,
    ( ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f211,plain,
    ( ~ spl7_18
    | ~ spl7_7
    | ~ spl7_21
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f209,f146,f154,f65,f143])).

fof(f143,plain,
    ( spl7_18
  <=> r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f154,plain,
    ( spl7_21
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f146,plain,
    ( spl7_19
  <=> ! [X0] :
        ( ~ r2_hidden(sK6(sK4,sK1,sK3),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f209,plain,
    ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl7_19 ),
    inference(resolution,[],[f147,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK4,sK1,sK3),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f146])).

fof(f193,plain,(
    spl7_21 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl7_21 ),
    inference(resolution,[],[f155,f80])).

fof(f80,plain,(
    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    inference(global_subsumption,[],[f26,f79])).

fof(f79,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(superposition,[],[f35,f76])).

fof(f76,plain,(
    k2_relat_1(sK3) = k2_relset_1(sK0,sK2,sK3) ),
    inference(resolution,[],[f34,f26])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f155,plain,
    ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | spl7_21 ),
    inference(avatar_component_clause,[],[f154])).

fof(f180,plain,
    ( ~ spl7_1
    | spl7_18 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl7_1
    | spl7_18 ),
    inference(resolution,[],[f144,f133])).

fof(f133,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f40,f132])).

fof(f40,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f144,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | spl7_18 ),
    inference(avatar_component_clause,[],[f143])).

fof(f148,plain,
    ( ~ spl7_7
    | ~ spl7_18
    | spl7_19
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f141,f126,f146,f143,f65])).

fof(f126,plain,
    ( spl7_17
  <=> ! [X6] :
        ( ~ r2_hidden(sK4,k10_relat_1(sK3,X6))
        | ~ m1_subset_1(sK6(sK4,X6,sK3),sK2)
        | ~ r2_hidden(sK6(sK4,X6,sK3),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK4,sK1,sK3),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
        | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
        | ~ v1_relat_1(sK3) )
    | ~ spl7_17 ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK4,sK1,sK3),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
        | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1)) )
    | ~ spl7_17 ),
    inference(resolution,[],[f129,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK6(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK6(sK4,X0,sK3),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK2))
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) )
    | ~ spl7_17 ),
    inference(resolution,[],[f127,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f127,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(sK6(sK4,X6,sK3),sK2)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X6))
        | ~ r2_hidden(sK6(sK4,X6,sK3),sK1) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f126])).

fof(f128,plain,
    ( spl7_17
    | ~ spl7_7
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f121,f55,f65,f126])).

fof(f55,plain,
    ( spl7_5
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(k4_tarski(sK4,X5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f121,plain,
    ( ! [X6] :
        ( ~ v1_relat_1(sK3)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X6))
        | ~ r2_hidden(sK6(sK4,X6,sK3),sK1)
        | ~ m1_subset_1(sK6(sK4,X6,sK3),sK2) )
    | ~ spl7_5 ),
    inference(resolution,[],[f30,f56])).

fof(f56,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(sK4,X5),sK3)
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2) )
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,
    ( spl7_8
    | ~ spl7_7
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f70,f46,f65,f72])).

fof(f70,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(sK5,k2_relat_1(sK3))
    | ~ spl7_3 ),
    inference(resolution,[],[f28,f47])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f69,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | spl7_7 ),
    inference(resolution,[],[f66,f58])).

fof(f58,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f33,f26])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f66,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f57,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f21,f55,f39])).

fof(f21,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f23,f46,f39])).

fof(f23,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f24,f42,f39])).

fof(f24,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:20:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (29483)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.49  % (29490)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.50  % (29479)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (29480)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (29482)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (29478)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (29481)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (29490)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (29481)Refutation not found, incomplete strategy% (29481)------------------------------
% 0.21/0.51  % (29481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29481)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29481)Memory used [KB]: 10618
% 0.21/0.51  % (29481)Time elapsed: 0.091 s
% 0.21/0.51  % (29481)------------------------------
% 0.21/0.51  % (29481)------------------------------
% 0.21/0.51  % (29488)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (29501)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  % (29499)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (29487)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (29493)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (29491)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.52  % (29501)Refutation not found, incomplete strategy% (29501)------------------------------
% 0.21/0.52  % (29501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29486)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f44,f48,f57,f69,f74,f128,f148,f180,f193,f211,f227,f231])).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    ~spl7_8 | ~spl7_2 | ~spl7_3 | ~spl7_24),
% 0.21/0.52    inference(avatar_split_clause,[],[f228,f225,f46,f42,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    spl7_8 <=> r2_hidden(sK5,k2_relat_1(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    spl7_2 <=> r2_hidden(sK5,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    spl7_3 <=> r2_hidden(k4_tarski(sK4,sK5),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    spl7_24 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | ~r2_hidden(X0,sK1) | ~r2_hidden(k4_tarski(sK4,X0),sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.52  fof(f228,plain,(
% 0.21/0.52    ~r2_hidden(sK5,sK1) | ~r2_hidden(sK5,k2_relat_1(sK3)) | (~spl7_3 | ~spl7_24)),
% 0.21/0.52    inference(resolution,[],[f226,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK4,sK5),sK3) | ~spl7_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f46])).
% 0.21/0.52  fof(f226,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(k4_tarski(sK4,X0),sK3) | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,k2_relat_1(sK3))) ) | ~spl7_24),
% 0.21/0.52    inference(avatar_component_clause,[],[f225])).
% 0.21/0.52  fof(f227,plain,(
% 0.21/0.52    ~spl7_7 | spl7_24 | spl7_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f223,f39,f225,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    spl7_7 <=> v1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    spl7_1 <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | ~r2_hidden(k4_tarski(sK4,X0),sK3) | ~r2_hidden(X0,sK1) | ~v1_relat_1(sK3)) ) | spl7_1),
% 0.21/0.52    inference(resolution,[],[f212,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.52  fof(f212,plain,(
% 0.21/0.52    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | spl7_1),
% 0.21/0.52    inference(forward_demodulation,[],[f53,f132])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ( ! [X10] : (k8_relset_1(sK0,sK2,sK3,X10) = k10_relat_1(sK3,X10)) )),
% 0.21/0.52    inference(resolution,[],[f37,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  % (29485)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (29501)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29501)Memory used [KB]: 10618
% 0.21/0.52  % (29501)Time elapsed: 0.059 s
% 0.21/0.52  % (29501)------------------------------
% 0.21/0.52  % (29501)------------------------------
% 0.21/0.52  % (29494)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.52  % (29498)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.52  fof(f9,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f8])).
% 0.21/0.52  fof(f8,conjecture,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | spl7_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f39])).
% 0.21/0.52  fof(f211,plain,(
% 0.21/0.52    ~spl7_18 | ~spl7_7 | ~spl7_21 | ~spl7_19),
% 0.21/0.52    inference(avatar_split_clause,[],[f209,f146,f154,f65,f143])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    spl7_18 <=> r2_hidden(sK4,k10_relat_1(sK3,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    spl7_21 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    spl7_19 <=> ! [X0] : (~r2_hidden(sK6(sK4,sK1,sK3),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl7_19),
% 0.21/0.52    inference(resolution,[],[f147,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK6(sK4,sK1,sK3),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK2))) ) | ~spl7_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f146])).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    spl7_21),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f191])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    $false | spl7_21),
% 0.21/0.52    inference(resolution,[],[f155,f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.21/0.52    inference(global_subsumption,[],[f26,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.52    inference(superposition,[],[f35,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    k2_relat_1(sK3) = k2_relset_1(sK0,sK2,sK3)),
% 0.21/0.52    inference(resolution,[],[f34,f26])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(X2) = k2_relset_1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | spl7_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f154])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    ~spl7_1 | spl7_18),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f178])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    $false | (~spl7_1 | spl7_18)),
% 0.21/0.52    inference(resolution,[],[f144,f133])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl7_1),
% 0.21/0.52    inference(backward_demodulation,[],[f40,f132])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | ~spl7_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f39])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | spl7_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f143])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ~spl7_7 | ~spl7_18 | spl7_19 | ~spl7_17),
% 0.21/0.52    inference(avatar_split_clause,[],[f141,f126,f146,f143,f65])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    spl7_17 <=> ! [X6] : (~r2_hidden(sK4,k10_relat_1(sK3,X6)) | ~m1_subset_1(sK6(sK4,X6,sK3),sK2) | ~r2_hidden(sK6(sK4,X6,sK3),sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK6(sK4,sK1,sK3),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK2)) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~v1_relat_1(sK3)) ) | ~spl7_17),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f135])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK6(sK4,sK1,sK3),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK2)) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1))) ) | ~spl7_17),
% 0.21/0.52    inference(resolution,[],[f129,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK6(sK4,X0,sK3),sK1) | ~r2_hidden(sK6(sK4,X0,sK3),X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK2)) | ~r2_hidden(sK4,k10_relat_1(sK3,X0))) ) | ~spl7_17),
% 0.21/0.52    inference(resolution,[],[f127,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    ( ! [X6] : (~m1_subset_1(sK6(sK4,X6,sK3),sK2) | ~r2_hidden(sK4,k10_relat_1(sK3,X6)) | ~r2_hidden(sK6(sK4,X6,sK3),sK1)) ) | ~spl7_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f126])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    spl7_17 | ~spl7_7 | ~spl7_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f121,f55,f65,f126])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    spl7_5 <=> ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    ( ! [X6] : (~v1_relat_1(sK3) | ~r2_hidden(sK4,k10_relat_1(sK3,X6)) | ~r2_hidden(sK6(sK4,X6,sK3),sK1) | ~m1_subset_1(sK6(sK4,X6,sK3),sK2)) ) | ~spl7_5),
% 0.21/0.52    inference(resolution,[],[f30,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X5] : (~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2)) ) | ~spl7_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f55])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl7_8 | ~spl7_7 | ~spl7_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f70,f46,f65,f72])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ~v1_relat_1(sK3) | r2_hidden(sK5,k2_relat_1(sK3)) | ~spl7_3),
% 0.21/0.52    inference(resolution,[],[f28,f47])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X1,k2_relat_1(X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl7_7),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    $false | spl7_7),
% 0.21/0.52    inference(resolution,[],[f66,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    v1_relat_1(sK3)),
% 0.21/0.52    inference(resolution,[],[f33,f26])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ~v1_relat_1(sK3) | spl7_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f65])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ~spl7_1 | spl7_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f21,f55,f39])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    spl7_1 | spl7_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f23,f46,f39])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK4,sK5),sK3) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    spl7_1 | spl7_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f24,f42,f39])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    r2_hidden(sK5,sK1) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (29490)------------------------------
% 0.21/0.52  % (29490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29490)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (29490)Memory used [KB]: 10746
% 0.21/0.52  % (29490)Time elapsed: 0.100 s
% 0.21/0.52  % (29490)------------------------------
% 0.21/0.52  % (29490)------------------------------
% 0.21/0.52  % (29488)Refutation not found, incomplete strategy% (29488)------------------------------
% 0.21/0.52  % (29488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29494)Refutation not found, incomplete strategy% (29494)------------------------------
% 0.21/0.52  % (29494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29494)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  % (29495)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  
% 0.21/0.52  % (29494)Memory used [KB]: 1663
% 0.21/0.52  % (29494)Time elapsed: 0.107 s
% 0.21/0.52  % (29494)------------------------------
% 0.21/0.52  % (29494)------------------------------
% 0.21/0.52  % (29496)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.52  % (29485)Refutation not found, incomplete strategy% (29485)------------------------------
% 0.21/0.52  % (29485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29477)Success in time 0.163 s
%------------------------------------------------------------------------------
