%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 119 expanded)
%              Number of leaves         :   21 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :  199 ( 299 expanded)
%              Number of equality atoms :   25 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f65,f84,f90,f107,f121,f126,f132,f133])).

fof(f133,plain,
    ( sK3 != k8_relat_1(sK2,sK3)
    | r2_relset_1(sK0,sK1,k8_relat_1(sK2,sK3),sK3)
    | ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f132,plain,
    ( spl4_10
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f127,f123,f104,f62,f129])).

fof(f129,plain,
    ( spl4_10
  <=> sK3 = k8_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f62,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f104,plain,
    ( spl4_7
  <=> r1_tarski(k2_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f123,plain,
    ( spl4_9
  <=> k8_relat_1(sK1,sK3) = k8_relat_1(sK2,k8_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f127,plain,
    ( sK3 = k8_relat_1(sK2,sK3)
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f125,f108])).

fof(f108,plain,
    ( sK3 = k8_relat_1(sK1,sK3)
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f64,f106,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f106,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f64,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f125,plain,
    ( k8_relat_1(sK1,sK3) = k8_relat_1(sK2,k8_relat_1(sK1,sK3))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f126,plain,
    ( spl4_9
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f75,f62,f44,f123])).

fof(f44,plain,
    ( spl4_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f75,plain,
    ( k8_relat_1(sK1,sK3) = k8_relat_1(sK2,k8_relat_1(sK1,sK3))
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f46,f64,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

fof(f46,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f121,plain,
    ( ~ spl4_8
    | ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f94,f54,f49,f118])).

fof(f118,plain,
    ( spl4_8
  <=> r2_relset_1(sK0,sK1,k8_relat_1(sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f49,plain,
    ( spl4_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f54,plain,
    ( spl4_3
  <=> r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f94,plain,
    ( ~ r2_relset_1(sK0,sK1,k8_relat_1(sK2,sK3),sK3)
    | ~ spl4_2
    | spl4_3 ),
    inference(superposition,[],[f56,f73])).

fof(f73,plain,
    ( ! [X0] : k6_relset_1(sK0,sK1,X0,sK3) = k8_relat_1(X0,sK3)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f51,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f51,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f56,plain,
    ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f107,plain,
    ( spl4_7
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f85,f81,f62,f104])).

fof(f81,plain,
    ( spl4_5
  <=> v5_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f85,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f64,f83,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f83,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f90,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f69,f49,f87])).

fof(f87,plain,
    ( spl4_6
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f69,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f51,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f84,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f66,f49,f81])).

fof(f66,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f51,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f65,plain,
    ( spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f58,f49,f62])).

fof(f58,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f32,f51,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f32,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f57,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f30,f54])).

fof(f30,plain,(
    ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).

fof(f52,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f28,f49])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f29,f44])).

fof(f29,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (6151)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.43  % (6151)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f134,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f47,f52,f57,f65,f84,f90,f107,f121,f126,f132,f133])).
% 0.20/0.43  fof(f133,plain,(
% 0.20/0.43    sK3 != k8_relat_1(sK2,sK3) | r2_relset_1(sK0,sK1,k8_relat_1(sK2,sK3),sK3) | ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.20/0.43    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.43  fof(f132,plain,(
% 0.20/0.43    spl4_10 | ~spl4_4 | ~spl4_7 | ~spl4_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f127,f123,f104,f62,f129])).
% 0.20/0.43  fof(f129,plain,(
% 0.20/0.43    spl4_10 <=> sK3 = k8_relat_1(sK2,sK3)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    spl4_4 <=> v1_relat_1(sK3)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.43  fof(f104,plain,(
% 0.20/0.43    spl4_7 <=> r1_tarski(k2_relat_1(sK3),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.43  fof(f123,plain,(
% 0.20/0.43    spl4_9 <=> k8_relat_1(sK1,sK3) = k8_relat_1(sK2,k8_relat_1(sK1,sK3))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.43  fof(f127,plain,(
% 0.20/0.43    sK3 = k8_relat_1(sK2,sK3) | (~spl4_4 | ~spl4_7 | ~spl4_9)),
% 0.20/0.43    inference(forward_demodulation,[],[f125,f108])).
% 0.20/0.43  fof(f108,plain,(
% 0.20/0.43    sK3 = k8_relat_1(sK1,sK3) | (~spl4_4 | ~spl4_7)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f64,f106,f33])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) )),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.20/0.43  fof(f106,plain,(
% 0.20/0.43    r1_tarski(k2_relat_1(sK3),sK1) | ~spl4_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f104])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    v1_relat_1(sK3) | ~spl4_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f62])).
% 0.20/0.43  fof(f125,plain,(
% 0.20/0.43    k8_relat_1(sK1,sK3) = k8_relat_1(sK2,k8_relat_1(sK1,sK3)) | ~spl4_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f123])).
% 0.20/0.43  fof(f126,plain,(
% 0.20/0.43    spl4_9 | ~spl4_1 | ~spl4_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f75,f62,f44,f123])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    spl4_1 <=> r1_tarski(sK1,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    k8_relat_1(sK1,sK3) = k8_relat_1(sK2,k8_relat_1(sK1,sK3)) | (~spl4_1 | ~spl4_4)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f46,f64,f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.43    inference(flattening,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    r1_tarski(sK1,sK2) | ~spl4_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f44])).
% 0.20/0.43  fof(f121,plain,(
% 0.20/0.43    ~spl4_8 | ~spl4_2 | spl4_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f94,f54,f49,f118])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    spl4_8 <=> r2_relset_1(sK0,sK1,k8_relat_1(sK2,sK3),sK3)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    spl4_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    spl4_3 <=> r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.43  fof(f94,plain,(
% 0.20/0.43    ~r2_relset_1(sK0,sK1,k8_relat_1(sK2,sK3),sK3) | (~spl4_2 | spl4_3)),
% 0.20/0.43    inference(superposition,[],[f56,f73])).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    ( ! [X0] : (k6_relset_1(sK0,sK1,X0,sK3) = k8_relat_1(X0,sK3)) ) | ~spl4_2),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f51,f38])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f49])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    ~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) | spl4_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f54])).
% 0.20/0.43  fof(f107,plain,(
% 0.20/0.43    spl4_7 | ~spl4_4 | ~spl4_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f85,f81,f62,f104])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    spl4_5 <=> v5_relat_1(sK3,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.43  fof(f85,plain,(
% 0.20/0.43    r1_tarski(k2_relat_1(sK3),sK1) | (~spl4_4 | ~spl4_5)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f64,f83,f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(nnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    v5_relat_1(sK3,sK1) | ~spl4_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f81])).
% 0.20/0.43  fof(f90,plain,(
% 0.20/0.43    spl4_6 | ~spl4_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f69,f49,f87])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    spl4_6 <=> r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    r2_relset_1(sK0,sK1,sK3,sK3) | ~spl4_2),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f51,f42])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.43    inference(equality_resolution,[],[f40])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(nnf_transformation,[],[f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(flattening,[],[f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    spl4_5 | ~spl4_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f66,f49,f81])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    v5_relat_1(sK3,sK1) | ~spl4_2),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f51,f37])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.20/0.43    inference(pure_predicate_removal,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    spl4_4 | ~spl4_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f58,f49,f62])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    v1_relat_1(sK3) | ~spl4_2),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f32,f51,f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    ~spl4_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f30,f54])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(flattening,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 0.20/0.43    inference(negated_conjecture,[],[f9])).
% 0.20/0.43  fof(f9,conjecture,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    spl4_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f28,f49])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    spl4_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f29,f44])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    r1_tarski(sK1,sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (6151)------------------------------
% 0.20/0.43  % (6151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (6151)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (6151)Memory used [KB]: 10618
% 0.20/0.43  % (6151)Time elapsed: 0.009 s
% 0.20/0.43  % (6151)------------------------------
% 0.20/0.43  % (6151)------------------------------
% 0.20/0.44  % (6123)Success in time 0.08 s
%------------------------------------------------------------------------------
