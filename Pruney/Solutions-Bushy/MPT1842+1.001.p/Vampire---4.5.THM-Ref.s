%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1842+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   50 (  75 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  122 ( 196 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f45,f52,f74,f89,f94])).

fof(f94,plain,
    ( spl2_2
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl2_2
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f92,f32])).

fof(f32,plain,
    ( ~ v1_zfmisc_1(sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_2
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f92,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl2_9 ),
    inference(superposition,[],[f18,f78])).

fof(f78,plain,
    ( sK0 = k1_tarski(sK1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_9
  <=> sK0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f18,plain,(
    ! [X0] : v1_zfmisc_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_zfmisc_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_zfmisc_1)).

fof(f89,plain,
    ( sK0 != k6_domain_1(sK0,sK1)
    | k6_domain_1(sK0,sK1) != k1_tarski(sK1)
    | sK0 = k1_tarski(sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f74,plain,
    ( spl2_8
    | spl2_1
    | ~ spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f62,f42,f35,f25,f71])).

fof(f71,plain,
    ( spl2_8
  <=> sK0 = k6_domain_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f25,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f35,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f42,plain,
    ( spl2_4
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f62,plain,
    ( sK0 = k6_domain_1(sK0,sK1)
    | spl2_1
    | ~ spl2_3
    | spl2_4 ),
    inference(subsumption_resolution,[],[f61,f44])).

fof(f44,plain,
    ( ~ v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f61,plain,
    ( sK0 = k6_domain_1(sK0,sK1)
    | v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | spl2_1
    | ~ spl2_3 ),
    inference(resolution,[],[f46,f37])).

fof(f37,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f46,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | sK0 = k6_domain_1(sK0,X0)
        | v1_subset_1(k6_domain_1(sK0,X0),sK0) )
    | spl2_1 ),
    inference(resolution,[],[f39,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f39,plain,
    ( ! [X0] :
        ( m1_subset_1(k6_domain_1(sK0,X0),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(X0,sK0) )
    | spl2_1 ),
    inference(resolution,[],[f27,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

% (14137)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f27,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f52,plain,
    ( spl2_5
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f47,f35,f25,f49])).

fof(f49,plain,
    ( spl2_5
  <=> k6_domain_1(sK0,sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f47,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | spl2_1
    | ~ spl2_3 ),
    inference(resolution,[],[f40,f37])).

fof(f40,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK0)
        | k1_tarski(X1) = k6_domain_1(sK0,X1) )
    | spl2_1 ),
    inference(resolution,[],[f27,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f45,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f15,f42])).

fof(f15,plain,(
    ~ v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( ~ v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

fof(f38,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f14,f35])).

fof(f14,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f33,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    ~ v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f28,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f16,f25])).

fof(f16,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
