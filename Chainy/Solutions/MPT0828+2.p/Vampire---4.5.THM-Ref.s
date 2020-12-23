%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0828+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:50 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   51 (  93 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  137 ( 304 expanded)
%              Number of equality atoms :   15 (  51 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7387,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f7231,f7313,f7364,f7374,f7386])).

fof(f7386,plain,(
    spl314_4 ),
    inference(avatar_contradiction_clause,[],[f7385])).

fof(f7385,plain,
    ( $false
    | spl314_4 ),
    inference(subsumption_resolution,[],[f7380,f3343])).

fof(f3343,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK7))) ),
    inference(cnf_transformation,[],[f2529])).

fof(f2529,plain,
    ( ( ~ r1_tarski(sK8,k2_relset_1(sK8,sK7,sK9))
      | sK8 != k1_relset_1(sK8,sK7,sK9) )
    & r1_tarski(k6_relat_1(sK8),sK9)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK7))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f1271,f2528])).

fof(f2528,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
          | k1_relset_1(X1,X0,X2) != X1 )
        & r1_tarski(k6_relat_1(X1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( ~ r1_tarski(sK8,k2_relset_1(sK8,sK7,sK9))
        | sK8 != k1_relset_1(sK8,sK7,sK9) )
      & r1_tarski(k6_relat_1(sK8),sK9)
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK7))) ) ),
    introduced(choice_axiom,[])).

fof(f1271,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
        | k1_relset_1(X1,X0,X2) != X1 )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f1270])).

fof(f1270,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
        | k1_relset_1(X1,X0,X2) != X1 )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f1238])).

fof(f1238,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
            & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1237])).

fof(f1237,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
          & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relset_1)).

fof(f7380,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK7)))
    | spl314_4 ),
    inference(resolution,[],[f7378,f4931])).

fof(f4931,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2278])).

fof(f2278,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1214])).

fof(f1214,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f7378,plain,
    ( ~ m1_subset_1(k1_relset_1(sK8,sK7,sK9),k1_zfmisc_1(sK8))
    | spl314_4 ),
    inference(resolution,[],[f7363,f4670])).

fof(f4670,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3085])).

fof(f3085,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f7363,plain,
    ( ~ r1_tarski(k1_relset_1(sK8,sK7,sK9),sK8)
    | spl314_4 ),
    inference(avatar_component_clause,[],[f7361])).

fof(f7361,plain,
    ( spl314_4
  <=> r1_tarski(k1_relset_1(sK8,sK7,sK9),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl314_4])])).

fof(f7374,plain,(
    spl314_3 ),
    inference(avatar_contradiction_clause,[],[f7373])).

fof(f7373,plain,
    ( $false
    | spl314_3 ),
    inference(subsumption_resolution,[],[f7372,f3343])).

fof(f7372,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK7)))
    | spl314_3 ),
    inference(subsumption_resolution,[],[f7366,f3344])).

fof(f3344,plain,(
    r1_tarski(k6_relat_1(sK8),sK9) ),
    inference(cnf_transformation,[],[f2529])).

fof(f7366,plain,
    ( ~ r1_tarski(k6_relat_1(sK8),sK9)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK7)))
    | spl314_3 ),
    inference(resolution,[],[f7359,f5208])).

fof(f5208,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k1_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2450])).

fof(f2450,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f2449])).

fof(f2449,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1236])).

fof(f1236,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

fof(f7359,plain,
    ( ~ r1_tarski(sK8,k1_relset_1(sK8,sK7,sK9))
    | spl314_3 ),
    inference(avatar_component_clause,[],[f7357])).

fof(f7357,plain,
    ( spl314_3
  <=> r1_tarski(sK8,k1_relset_1(sK8,sK7,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl314_3])])).

fof(f7364,plain,
    ( ~ spl314_3
    | ~ spl314_4
    | spl314_1 ),
    inference(avatar_split_clause,[],[f7242,f7224,f7361,f7357])).

fof(f7224,plain,
    ( spl314_1
  <=> sQ313_eqProxy(sK8,k1_relset_1(sK8,sK7,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl314_1])])).

fof(f7242,plain,
    ( ~ r1_tarski(k1_relset_1(sK8,sK7,sK9),sK8)
    | ~ r1_tarski(sK8,k1_relset_1(sK8,sK7,sK9))
    | spl314_1 ),
    inference(resolution,[],[f6345,f7226])).

fof(f7226,plain,
    ( ~ sQ313_eqProxy(sK8,k1_relset_1(sK8,sK7,sK9))
    | spl314_1 ),
    inference(avatar_component_clause,[],[f7224])).

fof(f6345,plain,(
    ! [X0,X1] :
      ( sQ313_eqProxy(X0,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f4618,f5760])).

fof(f5760,plain,(
    ! [X1,X0] :
      ( sQ313_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ313_eqProxy])])).

fof(f4618,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3032])).

fof(f3032,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f3031])).

fof(f3031,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f7313,plain,(
    spl314_2 ),
    inference(avatar_contradiction_clause,[],[f7312])).

fof(f7312,plain,
    ( $false
    | spl314_2 ),
    inference(subsumption_resolution,[],[f7311,f3343])).

fof(f7311,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK7)))
    | spl314_2 ),
    inference(subsumption_resolution,[],[f7307,f3344])).

fof(f7307,plain,
    ( ~ r1_tarski(k6_relat_1(sK8),sK9)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK7)))
    | spl314_2 ),
    inference(resolution,[],[f5209,f7230])).

fof(f7230,plain,
    ( ~ r1_tarski(sK8,k2_relset_1(sK8,sK7,sK9))
    | spl314_2 ),
    inference(avatar_component_clause,[],[f7228])).

fof(f7228,plain,
    ( spl314_2
  <=> r1_tarski(sK8,k2_relset_1(sK8,sK7,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl314_2])])).

fof(f5209,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2450])).

fof(f7231,plain,
    ( ~ spl314_1
    | ~ spl314_2 ),
    inference(avatar_split_clause,[],[f5779,f7228,f7224])).

fof(f5779,plain,
    ( ~ r1_tarski(sK8,k2_relset_1(sK8,sK7,sK9))
    | ~ sQ313_eqProxy(sK8,k1_relset_1(sK8,sK7,sK9)) ),
    inference(equality_proxy_replacement,[],[f3345,f5760])).

fof(f3345,plain,
    ( ~ r1_tarski(sK8,k2_relset_1(sK8,sK7,sK9))
    | sK8 != k1_relset_1(sK8,sK7,sK9) ),
    inference(cnf_transformation,[],[f2529])).
%------------------------------------------------------------------------------
