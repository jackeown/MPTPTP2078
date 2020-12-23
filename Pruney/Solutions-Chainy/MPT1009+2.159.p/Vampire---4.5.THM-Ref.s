%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 284 expanded)
%              Number of leaves         :   23 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :  293 ( 755 expanded)
%              Number of equality atoms :   95 ( 269 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f95,f103,f117,f123,f126,f147,f150,f155])).

fof(f155,plain,
    ( ~ spl5_5
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl5_5
    | spl5_8 ),
    inference(resolution,[],[f152,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f152,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK4),sK2))
    | ~ spl5_5
    | spl5_8 ),
    inference(resolution,[],[f151,f127])).

fof(f127,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK2)))
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f60,f115])).

fof(f115,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_5
  <=> k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f36,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK4,k1_tarski(sK1),sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f16,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
      & k1_xboole_0 != sK2
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK4,k1_tarski(sK1),sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f151,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl5_8 ),
    inference(resolution,[],[f148,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f148,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_8 ),
    inference(resolution,[],[f146,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f44,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

fof(f146,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl5_8
  <=> r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f150,plain,
    ( ~ spl5_5
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl5_5
    | spl5_7 ),
    inference(resolution,[],[f142,f127])).

fof(f142,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK2)))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl5_7
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f147,plain,
    ( ~ spl5_7
    | ~ spl5_8
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f138,f120,f113,f144,f140])).

fof(f120,plain,
    ( spl5_6
  <=> k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f138,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK2)))
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(superposition,[],[f132,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f132,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK3),k2_relset_1(k1_relat_1(sK4),sK2,sK4))
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f124,f115])).

fof(f124,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK3),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4))
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f76,f122])).

fof(f122,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f120])).

fof(f76,plain,(
    ~ r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(backward_demodulation,[],[f59,f75])).

fof(f75,plain,(
    ! [X0] : k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(resolution,[],[f56,f60])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f59,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(definition_unfolding,[],[f38,f58,f58])).

fof(f38,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f126,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f111,f60])).

fof(f111,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl5_4
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f123,plain,
    ( spl5_6
    | ~ spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f118,f88,f80,f120])).

fof(f80,plain,
    ( spl5_1
  <=> v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f88,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f118,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2)
    | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) ),
    inference(resolution,[],[f92,f60])).

% (9057)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X0)))
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK4,k2_enumset1(X1,X1,X1,X1),X0)
      | k2_relset_1(k2_enumset1(X1,X1,X1,X1),X0,sK4) = k2_enumset1(k1_funct_1(sK4,X1),k1_funct_1(sK4,X1),k1_funct_1(sK4,X1),k1_funct_1(sK4,X1)) ) ),
    inference(resolution,[],[f62,f34])).

fof(f34,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1)))
      | ~ v1_funct_2(X2,k2_enumset1(X0,X0,X0,X0),X1)
      | k2_relset_1(k2_enumset1(X0,X0,X0,X0),X1,X2) = k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0)) ) ),
    inference(definition_unfolding,[],[f55,f58,f58,f58,f58])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      | ~ v1_funct_2(X2,k1_tarski(X0),X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      | ~ v1_funct_2(X2,k1_tarski(X0),X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      | ~ v1_funct_2(X2,k1_tarski(X0),X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(f117,plain,
    ( ~ spl5_4
    | spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f107,f84,f113,f109])).

fof(f84,plain,
    ( spl5_2
  <=> k2_enumset1(sK1,sK1,sK1,sK1) = k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f107,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | ~ spl5_2 ),
    inference(superposition,[],[f47,f86])).

fof(f86,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

% (9060)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

% (9058)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f103,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | ~ spl5_3 ),
    inference(trivial_inequality_removal,[],[f101])).

fof(f101,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl5_3 ),
    inference(superposition,[],[f37,f90])).

fof(f90,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f37,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f95,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl5_1 ),
    inference(resolution,[],[f82,f61])).

fof(f61,plain,(
    v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f35,f58])).

fof(f35,plain,(
    v1_funct_2(sK4,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,
    ( ~ v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f91,plain,
    ( ~ spl5_1
    | spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f78,f88,f84,f80])).

fof(f78,plain,
    ( k1_xboole_0 = sK2
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4)
    | ~ v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(resolution,[],[f77,f60])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X2
      | k1_relset_1(X1,X2,X0) = X1
      | ~ v1_funct_2(X0,X1,X2) ) ),
    inference(resolution,[],[f48,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f23,f27])).

fof(f27,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:50:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (9067)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (9055)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (9075)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (9067)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 1.24/0.52  % (9084)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.24/0.52  % SZS output start Proof for theBenchmark
% 1.24/0.52  fof(f156,plain,(
% 1.24/0.52    $false),
% 1.24/0.52    inference(avatar_sat_refutation,[],[f91,f95,f103,f117,f123,f126,f147,f150,f155])).
% 1.24/0.52  fof(f155,plain,(
% 1.24/0.52    ~spl5_5 | spl5_8),
% 1.24/0.52    inference(avatar_contradiction_clause,[],[f153])).
% 1.24/0.52  fof(f153,plain,(
% 1.24/0.52    $false | (~spl5_5 | spl5_8)),
% 1.24/0.52    inference(resolution,[],[f152,f42])).
% 1.24/0.52  fof(f42,plain,(
% 1.24/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.24/0.52    inference(cnf_transformation,[],[f5])).
% 1.24/0.52  fof(f5,axiom,(
% 1.24/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.24/0.52  fof(f152,plain,(
% 1.24/0.52    ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK4),sK2)) | (~spl5_5 | spl5_8)),
% 1.24/0.52    inference(resolution,[],[f151,f127])).
% 1.24/0.52  fof(f127,plain,(
% 1.24/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK2))) | ~spl5_5),
% 1.24/0.52    inference(backward_demodulation,[],[f60,f115])).
% 1.24/0.52  fof(f115,plain,(
% 1.24/0.52    k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4) | ~spl5_5),
% 1.24/0.52    inference(avatar_component_clause,[],[f113])).
% 1.24/0.52  fof(f113,plain,(
% 1.24/0.52    spl5_5 <=> k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)),
% 1.24/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.24/0.52  fof(f60,plain,(
% 1.24/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 1.24/0.52    inference(definition_unfolding,[],[f36,f58])).
% 1.24/0.52  fof(f58,plain,(
% 1.24/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.24/0.52    inference(definition_unfolding,[],[f39,f57])).
% 1.24/0.52  fof(f57,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.24/0.52    inference(definition_unfolding,[],[f43,f45])).
% 1.24/0.52  fof(f45,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f3])).
% 1.24/0.52  fof(f3,axiom,(
% 1.24/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.24/0.52  fof(f43,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f2])).
% 1.24/0.52  fof(f2,axiom,(
% 1.24/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.24/0.52  fof(f39,plain,(
% 1.24/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f1])).
% 1.24/0.52  fof(f1,axiom,(
% 1.24/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.24/0.52  fof(f36,plain,(
% 1.24/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 1.24/0.52    inference(cnf_transformation,[],[f30])).
% 1.24/0.52  fof(f30,plain,(
% 1.24/0.52    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4)),
% 1.24/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f16,f29])).
% 1.24/0.52  fof(f29,plain,(
% 1.24/0.52    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4))),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f16,plain,(
% 1.24/0.52    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 1.24/0.52    inference(flattening,[],[f15])).
% 1.24/0.52  fof(f15,plain,(
% 1.24/0.52    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 1.24/0.52    inference(ennf_transformation,[],[f14])).
% 1.24/0.52  fof(f14,negated_conjecture,(
% 1.24/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.24/0.52    inference(negated_conjecture,[],[f13])).
% 1.24/0.52  fof(f13,conjecture,(
% 1.24/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 1.24/0.52  fof(f151,plain,(
% 1.24/0.52    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl5_8),
% 1.24/0.52    inference(resolution,[],[f148,f41])).
% 1.24/0.52  fof(f41,plain,(
% 1.24/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f18])).
% 1.24/0.52  fof(f18,plain,(
% 1.24/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.24/0.52    inference(ennf_transformation,[],[f4])).
% 1.24/0.52  fof(f4,axiom,(
% 1.24/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.24/0.52  fof(f148,plain,(
% 1.24/0.52    ~v1_relat_1(sK4) | spl5_8),
% 1.24/0.52    inference(resolution,[],[f146,f70])).
% 1.24/0.52  fof(f70,plain,(
% 1.24/0.52    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.24/0.52    inference(duplicate_literal_removal,[],[f69])).
% 1.24/0.52  fof(f69,plain,(
% 1.24/0.52    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.24/0.52    inference(superposition,[],[f44,f40])).
% 1.24/0.52  fof(f40,plain,(
% 1.24/0.52    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f17])).
% 1.24/0.52  fof(f17,plain,(
% 1.24/0.52    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.24/0.52    inference(ennf_transformation,[],[f6])).
% 1.24/0.52  fof(f6,axiom,(
% 1.24/0.52    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.24/0.52  fof(f44,plain,(
% 1.24/0.52    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f19])).
% 1.24/0.52  fof(f19,plain,(
% 1.24/0.52    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.24/0.52    inference(ennf_transformation,[],[f7])).
% 1.24/0.52  fof(f7,axiom,(
% 1.24/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).
% 1.24/0.52  fof(f146,plain,(
% 1.24/0.52    ~r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) | spl5_8),
% 1.24/0.52    inference(avatar_component_clause,[],[f144])).
% 1.24/0.52  fof(f144,plain,(
% 1.24/0.52    spl5_8 <=> r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))),
% 1.24/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.24/0.52  fof(f150,plain,(
% 1.24/0.52    ~spl5_5 | spl5_7),
% 1.24/0.52    inference(avatar_contradiction_clause,[],[f149])).
% 1.24/0.52  fof(f149,plain,(
% 1.24/0.52    $false | (~spl5_5 | spl5_7)),
% 1.24/0.52    inference(resolution,[],[f142,f127])).
% 1.24/0.52  fof(f142,plain,(
% 1.24/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK2))) | spl5_7),
% 1.24/0.52    inference(avatar_component_clause,[],[f140])).
% 1.24/0.52  fof(f140,plain,(
% 1.24/0.52    spl5_7 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK2)))),
% 1.24/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.24/0.52  fof(f147,plain,(
% 1.24/0.52    ~spl5_7 | ~spl5_8 | ~spl5_5 | ~spl5_6),
% 1.24/0.52    inference(avatar_split_clause,[],[f138,f120,f113,f144,f140])).
% 1.24/0.52  fof(f120,plain,(
% 1.24/0.52    spl5_6 <=> k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4)),
% 1.24/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.24/0.52  fof(f138,plain,(
% 1.24/0.52    ~r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK2))) | (~spl5_5 | ~spl5_6)),
% 1.24/0.52    inference(superposition,[],[f132,f46])).
% 1.24/0.52  fof(f46,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.24/0.52    inference(cnf_transformation,[],[f20])).
% 1.24/0.52  fof(f20,plain,(
% 1.24/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.52    inference(ennf_transformation,[],[f9])).
% 1.24/0.52  fof(f9,axiom,(
% 1.24/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.24/0.52  fof(f132,plain,(
% 1.24/0.52    ~r1_tarski(k9_relat_1(sK4,sK3),k2_relset_1(k1_relat_1(sK4),sK2,sK4)) | (~spl5_5 | ~spl5_6)),
% 1.24/0.52    inference(backward_demodulation,[],[f124,f115])).
% 1.24/0.52  fof(f124,plain,(
% 1.24/0.52    ~r1_tarski(k9_relat_1(sK4,sK3),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4)) | ~spl5_6),
% 1.24/0.52    inference(backward_demodulation,[],[f76,f122])).
% 1.24/0.52  fof(f122,plain,(
% 1.24/0.52    k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) | ~spl5_6),
% 1.24/0.52    inference(avatar_component_clause,[],[f120])).
% 1.24/0.52  fof(f76,plain,(
% 1.24/0.52    ~r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))),
% 1.24/0.52    inference(backward_demodulation,[],[f59,f75])).
% 1.24/0.52  fof(f75,plain,(
% 1.24/0.52    ( ! [X0] : (k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0)) )),
% 1.24/0.52    inference(resolution,[],[f56,f60])).
% 1.24/0.52  fof(f56,plain,(
% 1.24/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f26])).
% 1.24/0.52  fof(f26,plain,(
% 1.24/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.52    inference(ennf_transformation,[],[f10])).
% 1.24/0.52  fof(f10,axiom,(
% 1.24/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.24/0.52  fof(f59,plain,(
% 1.24/0.52    ~r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))),
% 1.24/0.52    inference(definition_unfolding,[],[f38,f58,f58])).
% 1.24/0.52  fof(f38,plain,(
% 1.24/0.52    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))),
% 1.24/0.52    inference(cnf_transformation,[],[f30])).
% 1.24/0.52  fof(f126,plain,(
% 1.24/0.52    spl5_4),
% 1.24/0.52    inference(avatar_contradiction_clause,[],[f125])).
% 1.24/0.52  fof(f125,plain,(
% 1.24/0.52    $false | spl5_4),
% 1.24/0.52    inference(resolution,[],[f111,f60])).
% 1.24/0.52  fof(f111,plain,(
% 1.24/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) | spl5_4),
% 1.24/0.52    inference(avatar_component_clause,[],[f109])).
% 1.24/0.52  fof(f109,plain,(
% 1.24/0.52    spl5_4 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 1.24/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.24/0.52  fof(f123,plain,(
% 1.24/0.52    spl5_6 | ~spl5_1 | spl5_3),
% 1.24/0.52    inference(avatar_split_clause,[],[f118,f88,f80,f120])).
% 1.24/0.52  fof(f80,plain,(
% 1.24/0.52    spl5_1 <=> v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 1.24/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.24/0.52  fof(f88,plain,(
% 1.24/0.52    spl5_3 <=> k1_xboole_0 = sK2),
% 1.24/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.24/0.52  fof(f118,plain,(
% 1.24/0.52    k1_xboole_0 = sK2 | ~v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2) | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4)),
% 1.24/0.52    inference(resolution,[],[f92,f60])).
% 1.24/0.52  % (9057)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.52  fof(f92,plain,(
% 1.24/0.52    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X0))) | k1_xboole_0 = X0 | ~v1_funct_2(sK4,k2_enumset1(X1,X1,X1,X1),X0) | k2_relset_1(k2_enumset1(X1,X1,X1,X1),X0,sK4) = k2_enumset1(k1_funct_1(sK4,X1),k1_funct_1(sK4,X1),k1_funct_1(sK4,X1),k1_funct_1(sK4,X1))) )),
% 1.24/0.52    inference(resolution,[],[f62,f34])).
% 1.24/0.52  fof(f34,plain,(
% 1.24/0.52    v1_funct_1(sK4)),
% 1.24/0.52    inference(cnf_transformation,[],[f30])).
% 1.24/0.52  fof(f62,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1))) | ~v1_funct_2(X2,k2_enumset1(X0,X0,X0,X0),X1) | k2_relset_1(k2_enumset1(X0,X0,X0,X0),X1,X2) = k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0))) )),
% 1.24/0.52    inference(definition_unfolding,[],[f55,f58,f58,f58,f58])).
% 1.24/0.52  fof(f55,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) | ~v1_funct_2(X2,k1_tarski(X0),X1) | ~v1_funct_1(X2)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f25])).
% 1.24/0.52  fof(f25,plain,(
% 1.24/0.52    ! [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) | ~v1_funct_2(X2,k1_tarski(X0),X1) | ~v1_funct_1(X2))),
% 1.24/0.52    inference(flattening,[],[f24])).
% 1.24/0.52  fof(f24,plain,(
% 1.24/0.52    ! [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) | k1_xboole_0 = X1) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) | ~v1_funct_2(X2,k1_tarski(X0),X1) | ~v1_funct_1(X2)))),
% 1.24/0.52    inference(ennf_transformation,[],[f12])).
% 1.24/0.52  fof(f12,axiom,(
% 1.24/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).
% 1.24/0.52  fof(f117,plain,(
% 1.24/0.52    ~spl5_4 | spl5_5 | ~spl5_2),
% 1.24/0.52    inference(avatar_split_clause,[],[f107,f84,f113,f109])).
% 1.24/0.52  fof(f84,plain,(
% 1.24/0.52    spl5_2 <=> k2_enumset1(sK1,sK1,sK1,sK1) = k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4)),
% 1.24/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.24/0.52  fof(f107,plain,(
% 1.24/0.52    k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) | ~spl5_2),
% 1.24/0.52    inference(superposition,[],[f47,f86])).
% 1.24/0.52  fof(f86,plain,(
% 1.24/0.52    k2_enumset1(sK1,sK1,sK1,sK1) = k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) | ~spl5_2),
% 1.24/0.52    inference(avatar_component_clause,[],[f84])).
% 1.24/0.52  fof(f47,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.24/0.52    inference(cnf_transformation,[],[f21])).
% 1.24/0.52  % (9060)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.24/0.52  fof(f21,plain,(
% 1.24/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.52    inference(ennf_transformation,[],[f8])).
% 1.24/0.52  % (9058)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.24/0.52  fof(f8,axiom,(
% 1.24/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.24/0.52  fof(f103,plain,(
% 1.24/0.52    ~spl5_3),
% 1.24/0.52    inference(avatar_contradiction_clause,[],[f102])).
% 1.24/0.52  fof(f102,plain,(
% 1.24/0.52    $false | ~spl5_3),
% 1.24/0.52    inference(trivial_inequality_removal,[],[f101])).
% 1.24/0.52  fof(f101,plain,(
% 1.24/0.52    k1_xboole_0 != k1_xboole_0 | ~spl5_3),
% 1.24/0.52    inference(superposition,[],[f37,f90])).
% 1.24/0.52  fof(f90,plain,(
% 1.24/0.52    k1_xboole_0 = sK2 | ~spl5_3),
% 1.24/0.52    inference(avatar_component_clause,[],[f88])).
% 1.24/0.52  fof(f37,plain,(
% 1.24/0.52    k1_xboole_0 != sK2),
% 1.24/0.52    inference(cnf_transformation,[],[f30])).
% 1.24/0.52  fof(f95,plain,(
% 1.24/0.52    spl5_1),
% 1.24/0.52    inference(avatar_contradiction_clause,[],[f93])).
% 1.24/0.52  fof(f93,plain,(
% 1.24/0.52    $false | spl5_1),
% 1.24/0.52    inference(resolution,[],[f82,f61])).
% 1.24/0.52  fof(f61,plain,(
% 1.24/0.52    v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 1.24/0.52    inference(definition_unfolding,[],[f35,f58])).
% 1.24/0.52  fof(f35,plain,(
% 1.24/0.52    v1_funct_2(sK4,k1_tarski(sK1),sK2)),
% 1.24/0.52    inference(cnf_transformation,[],[f30])).
% 1.24/0.52  fof(f82,plain,(
% 1.24/0.52    ~v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2) | spl5_1),
% 1.24/0.52    inference(avatar_component_clause,[],[f80])).
% 1.24/0.52  fof(f91,plain,(
% 1.24/0.52    ~spl5_1 | spl5_2 | spl5_3),
% 1.24/0.52    inference(avatar_split_clause,[],[f78,f88,f84,f80])).
% 1.24/0.52  fof(f78,plain,(
% 1.24/0.52    k1_xboole_0 = sK2 | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) | ~v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 1.24/0.52    inference(resolution,[],[f77,f60])).
% 1.24/0.52  fof(f77,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X2 | k1_relset_1(X1,X2,X0) = X1 | ~v1_funct_2(X0,X1,X2)) )),
% 1.24/0.52    inference(resolution,[],[f48,f52])).
% 1.24/0.52  fof(f52,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.24/0.52    inference(cnf_transformation,[],[f33])).
% 1.24/0.52  fof(f33,plain,(
% 1.24/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.52    inference(nnf_transformation,[],[f28])).
% 1.24/0.52  fof(f28,plain,(
% 1.24/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.52    inference(definition_folding,[],[f23,f27])).
% 1.24/0.52  fof(f27,plain,(
% 1.24/0.52    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.24/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.24/0.52  fof(f23,plain,(
% 1.24/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.52    inference(flattening,[],[f22])).
% 1.24/0.52  fof(f22,plain,(
% 1.24/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.52    inference(ennf_transformation,[],[f11])).
% 1.24/0.52  fof(f11,axiom,(
% 1.24/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.24/0.52  fof(f48,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.24/0.52    inference(cnf_transformation,[],[f32])).
% 1.24/0.52  fof(f32,plain,(
% 1.24/0.52    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.24/0.52    inference(rectify,[],[f31])).
% 1.24/0.52  fof(f31,plain,(
% 1.24/0.52    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.24/0.52    inference(nnf_transformation,[],[f27])).
% 1.24/0.52  % SZS output end Proof for theBenchmark
% 1.24/0.52  % (9067)------------------------------
% 1.24/0.52  % (9067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (9067)Termination reason: Refutation
% 1.24/0.52  
% 1.24/0.52  % (9067)Memory used [KB]: 6268
% 1.24/0.52  % (9067)Time elapsed: 0.111 s
% 1.24/0.52  % (9067)------------------------------
% 1.24/0.52  % (9067)------------------------------
% 1.24/0.52  % (9054)Success in time 0.167 s
%------------------------------------------------------------------------------
