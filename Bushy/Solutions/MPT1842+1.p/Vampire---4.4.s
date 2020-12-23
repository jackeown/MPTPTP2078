%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t7_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:57 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   54 (  94 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :  130 ( 240 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f130,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f66,f70,f85,f95,f103,f120,f129])).

fof(f129,plain,
    ( spl4_3
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f127,f65])).

fof(f65,plain,
    ( ~ v1_zfmisc_1(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_3
  <=> ~ v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f127,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl4_18 ),
    inference(superposition,[],[f54,f119])).

fof(f119,plain,
    ( k1_tarski(sK1) = sK0
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_18
  <=> k1_tarski(sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f54,plain,(
    ! [X0] : v1_zfmisc_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : v1_zfmisc_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t7_tex_2.p',fc2_zfmisc_1)).

fof(f120,plain,
    ( spl4_18
    | spl4_11
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f108,f101,f93,f118])).

fof(f93,plain,
    ( spl4_11
  <=> ~ v1_subset_1(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f101,plain,
    ( spl4_14
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f108,plain,
    ( k1_tarski(sK1) = sK0
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f104,f94])).

fof(f94,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f104,plain,
    ( k1_tarski(sK1) = sK0
    | v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl4_14 ),
    inference(resolution,[],[f102,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t7_tex_2.p',d7_subset_1)).

fof(f102,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f101])).

fof(f103,plain,
    ( spl4_14
    | spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f77,f68,f60,f101])).

fof(f60,plain,
    ( spl4_1
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f68,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f77,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f76,f75])).

fof(f75,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f72,f61])).

fof(f61,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f72,plain,
    ( v1_xboole_0(sK0)
    | k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f69,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t7_tex_2.p',redefinition_k6_domain_1)).

fof(f69,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f76,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f73,f61])).

fof(f73,plain,
    ( v1_xboole_0(sK0)
    | m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f69,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t7_tex_2.p',dt_k6_domain_1)).

fof(f95,plain,
    ( ~ spl4_11
    | spl4_1
    | ~ spl4_4
    | spl4_9 ),
    inference(avatar_split_clause,[],[f86,f83,f68,f60,f93])).

fof(f83,plain,
    ( spl4_9
  <=> ~ v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f86,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f84,f75])).

fof(f84,plain,
    ( ~ v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f83])).

fof(f85,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f40,f83])).

fof(f40,plain,(
    ~ v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( ~ v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t7_tex_2.p',t7_tex_2)).

fof(f70,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f39,f68])).

fof(f39,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f42,f64])).

fof(f42,plain,(
    ~ v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f41,f60])).

fof(f41,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
