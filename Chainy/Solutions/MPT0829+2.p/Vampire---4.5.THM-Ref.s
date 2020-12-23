%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0829+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:50 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
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
fof(f7393,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f7237,f7318,f7356,f7373,f7392])).

fof(f7392,plain,(
    spl314_4 ),
    inference(avatar_contradiction_clause,[],[f7391])).

fof(f7391,plain,
    ( $false
    | spl314_4 ),
    inference(subsumption_resolution,[],[f7386,f3346])).

fof(f3346,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(cnf_transformation,[],[f2532])).

fof(f2532,plain,
    ( ( sK8 != k2_relset_1(sK7,sK8,sK9)
      | ~ r1_tarski(sK8,k1_relset_1(sK7,sK8,sK9)) )
    & r1_tarski(k6_relat_1(sK8),sK9)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f1272,f2531])).

fof(f2531,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
        & r1_tarski(k6_relat_1(X1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( sK8 != k2_relset_1(sK7,sK8,sK9)
        | ~ r1_tarski(sK8,k1_relset_1(sK7,sK8,sK9)) )
      & r1_tarski(k6_relat_1(sK8),sK9)
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ) ),
    introduced(choice_axiom,[])).

fof(f1272,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f1271])).

fof(f1271,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1239])).

fof(f1239,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1238])).

fof(f1238,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

fof(f7386,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | spl314_4 ),
    inference(resolution,[],[f7384,f4934])).

fof(f4934,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2279])).

fof(f2279,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1215])).

fof(f1215,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f7384,plain,
    ( ~ m1_subset_1(k2_relset_1(sK7,sK8,sK9),k1_zfmisc_1(sK8))
    | spl314_4 ),
    inference(resolution,[],[f7355,f4673])).

fof(f4673,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3088])).

fof(f3088,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f7355,plain,
    ( ~ r1_tarski(k2_relset_1(sK7,sK8,sK9),sK8)
    | spl314_4 ),
    inference(avatar_component_clause,[],[f7353])).

fof(f7353,plain,
    ( spl314_4
  <=> r1_tarski(k2_relset_1(sK7,sK8,sK9),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl314_4])])).

fof(f7373,plain,(
    spl314_3 ),
    inference(avatar_contradiction_clause,[],[f7372])).

fof(f7372,plain,
    ( $false
    | spl314_3 ),
    inference(subsumption_resolution,[],[f7371,f3346])).

fof(f7371,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | spl314_3 ),
    inference(subsumption_resolution,[],[f7365,f3347])).

fof(f3347,plain,(
    r1_tarski(k6_relat_1(sK8),sK9) ),
    inference(cnf_transformation,[],[f2532])).

fof(f7365,plain,
    ( ~ r1_tarski(k6_relat_1(sK8),sK9)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | spl314_3 ),
    inference(resolution,[],[f7351,f5214])).

fof(f5214,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2453])).

fof(f2453,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f2452])).

fof(f2452,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

fof(f7351,plain,
    ( ~ r1_tarski(sK8,k2_relset_1(sK7,sK8,sK9))
    | spl314_3 ),
    inference(avatar_component_clause,[],[f7349])).

fof(f7349,plain,
    ( spl314_3
  <=> r1_tarski(sK8,k2_relset_1(sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl314_3])])).

fof(f7356,plain,
    ( ~ spl314_3
    | ~ spl314_4
    | spl314_2 ),
    inference(avatar_split_clause,[],[f7248,f7234,f7353,f7349])).

fof(f7234,plain,
    ( spl314_2
  <=> sQ313_eqProxy(sK8,k2_relset_1(sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl314_2])])).

fof(f7248,plain,
    ( ~ r1_tarski(k2_relset_1(sK7,sK8,sK9),sK8)
    | ~ r1_tarski(sK8,k2_relset_1(sK7,sK8,sK9))
    | spl314_2 ),
    inference(resolution,[],[f6350,f7236])).

fof(f7236,plain,
    ( ~ sQ313_eqProxy(sK8,k2_relset_1(sK7,sK8,sK9))
    | spl314_2 ),
    inference(avatar_component_clause,[],[f7234])).

fof(f6350,plain,(
    ! [X0,X1] :
      ( sQ313_eqProxy(X0,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f4621,f5765])).

fof(f5765,plain,(
    ! [X1,X0] :
      ( sQ313_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ313_eqProxy])])).

fof(f4621,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3035])).

fof(f3035,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f3034])).

fof(f3034,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f7318,plain,(
    spl314_1 ),
    inference(avatar_contradiction_clause,[],[f7317])).

fof(f7317,plain,
    ( $false
    | spl314_1 ),
    inference(subsumption_resolution,[],[f7316,f3346])).

fof(f7316,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | spl314_1 ),
    inference(subsumption_resolution,[],[f7312,f3347])).

fof(f7312,plain,
    ( ~ r1_tarski(k6_relat_1(sK8),sK9)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | spl314_1 ),
    inference(resolution,[],[f5213,f7232])).

fof(f7232,plain,
    ( ~ r1_tarski(sK8,k1_relset_1(sK7,sK8,sK9))
    | spl314_1 ),
    inference(avatar_component_clause,[],[f7230])).

fof(f7230,plain,
    ( spl314_1
  <=> r1_tarski(sK8,k1_relset_1(sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl314_1])])).

fof(f5213,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k1_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2453])).

fof(f7237,plain,
    ( ~ spl314_1
    | ~ spl314_2 ),
    inference(avatar_split_clause,[],[f5784,f7234,f7230])).

fof(f5784,plain,
    ( ~ sQ313_eqProxy(sK8,k2_relset_1(sK7,sK8,sK9))
    | ~ r1_tarski(sK8,k1_relset_1(sK7,sK8,sK9)) ),
    inference(equality_proxy_replacement,[],[f3348,f5765])).

fof(f3348,plain,
    ( sK8 != k2_relset_1(sK7,sK8,sK9)
    | ~ r1_tarski(sK8,k1_relset_1(sK7,sK8,sK9)) ),
    inference(cnf_transformation,[],[f2532])).
%------------------------------------------------------------------------------
