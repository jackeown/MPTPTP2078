%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t1_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:29 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 102 expanded)
%              Number of leaves         :   13 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :  154 ( 290 expanded)
%              Number of equality atoms :   34 (  59 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f364,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f77,f81,f89,f93,f98,f146,f293,f362])).

fof(f362,plain,
    ( spl5_5
    | ~ spl5_58 ),
    inference(avatar_contradiction_clause,[],[f361])).

fof(f361,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_58 ),
    inference(subsumption_resolution,[],[f355,f60])).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t1_tex_2.p',fc1_xboole_0)).

fof(f355,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_5
    | ~ spl5_58 ),
    inference(superposition,[],[f80,f292])).

fof(f292,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl5_58
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f80,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_5
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f293,plain,
    ( spl5_58
    | ~ spl5_6
    | spl5_9
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f289,f144,f91,f87,f291])).

fof(f87,plain,
    ( spl5_6
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f91,plain,
    ( spl5_9
  <=> sK0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f144,plain,
    ( spl5_22
  <=> k1_tarski(sK2(sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f289,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f286,f92])).

fof(f92,plain,
    ( sK0 != sK1
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f286,plain,
    ( sK0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_6
    | ~ spl5_22 ),
    inference(resolution,[],[f151,f88])).

fof(f88,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0
        | k1_xboole_0 = X0 )
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f148,f145])).

fof(f145,plain,
    ( k1_tarski(sK2(sK1)) = sK1
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f144])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k1_tarski(sK2(sK1)) = X0
        | k1_xboole_0 = X0 )
    | ~ spl5_22 ),
    inference(superposition,[],[f53,f145])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t1_tex_2.p',t39_zfmisc_1)).

fof(f146,plain,
    ( spl5_22
    | spl5_1
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f108,f96,f75,f71,f144])).

fof(f71,plain,
    ( spl5_1
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f75,plain,
    ( spl5_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f96,plain,
    ( spl5_10
  <=> m1_subset_1(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f108,plain,
    ( k1_tarski(sK2(sK1)) = sK1
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f107,f85])).

fof(f85,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = sK1
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f83,f72])).

fof(f72,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f83,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = sK1
    | v1_xboole_0(sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f76,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t1_tex_2.p',d1_tex_2)).

fof(f76,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f107,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f103,f72])).

fof(f103,plain,
    ( v1_xboole_0(sK1)
    | k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | ~ spl5_10 ),
    inference(resolution,[],[f97,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t1_tex_2.p',redefinition_k6_domain_1)).

fof(f97,plain,
    ( m1_subset_1(sK2(sK1),sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f98,plain,
    ( spl5_10
    | spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f84,f75,f71,f96])).

fof(f84,plain,
    ( m1_subset_1(sK2(sK1),sK1)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f82,f72])).

fof(f82,plain,
    ( m1_subset_1(sK2(sK1),sK1)
    | v1_xboole_0(sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f76,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f93,plain,(
    ~ spl5_9 ),
    inference(avatar_split_clause,[],[f44,f91])).

fof(f44,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t1_tex_2.p',t1_tex_2)).

fof(f89,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f43,f87])).

fof(f43,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f81,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f45,f79])).

fof(f45,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f77,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f42,f75])).

fof(f42,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f41,f71])).

fof(f41,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
