%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:48 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 226 expanded)
%              Number of leaves         :   15 (  64 expanded)
%              Depth                    :   15
%              Number of atoms          :  208 ( 687 expanded)
%              Number of equality atoms :   47 ( 181 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f217,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f176,f210,f216])).

fof(f216,plain,(
    ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | ~ spl4_11 ),
    inference(resolution,[],[f175,f140])).

fof(f140,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f116,f139])).

fof(f139,plain,(
    k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f138,f87])).

fof(f87,plain,(
    k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f46,f52])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f31,f50])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f37])).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK3,k1_tarski(sK0),sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK3,k1_tarski(sK0),sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f138,plain,(
    k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3) ),
    inference(subsumption_resolution,[],[f137,f29])).

fof(f29,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f137,plain,
    ( k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f136,f53])).

fof(f53,plain,(
    v1_funct_2(sK3,k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f30,f50])).

fof(f30,plain,(
    v1_funct_2(sK3,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f136,plain,
    ( k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3)
    | ~ v1_funct_2(sK3,k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f135,f32])).

fof(f32,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f135,plain,
    ( k1_xboole_0 = sK1
    | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3)
    | ~ v1_funct_2(sK3,k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f54,f52])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(X0,X0,X0),X1)))
      | k1_xboole_0 = X1
      | k2_relset_1(k1_enumset1(X0,X0,X0),X1,X2) = k1_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0))
      | ~ v1_funct_2(X2,k1_enumset1(X0,X0,X0),X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f47,f50,f50,f50,f50])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      | ~ v1_funct_2(X2,k1_tarski(X0),X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      | ~ v1_funct_2(X2,k1_tarski(X0),X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      | ~ v1_funct_2(X2,k1_tarski(X0),X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(f116,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f51,f112])).

fof(f112,plain,(
    ! [X0] : k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f49,f52])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f51,plain,(
    ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f33,f50,f50])).

fof(f33,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f175,plain,
    ( ! [X1] : r1_tarski(k9_relat_1(sK3,X1),k2_relat_1(sK3))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl4_11
  <=> ! [X1] : r1_tarski(k9_relat_1(sK3,X1),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f210,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f208,f61])).

fof(f61,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f59,f36])).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f59,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    inference(resolution,[],[f35,f52])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f208,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_10 ),
    inference(subsumption_resolution,[],[f207,f29])).

fof(f207,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_10 ),
    inference(subsumption_resolution,[],[f205,f55])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f205,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_10 ),
    inference(resolution,[],[f172,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f172,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl4_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f176,plain,
    ( ~ spl4_10
    | spl4_11 ),
    inference(avatar_split_clause,[],[f155,f174,f170])).

fof(f155,plain,(
    ! [X1] :
      ( r1_tarski(k9_relat_1(sK3,X1),k2_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ) ),
    inference(superposition,[],[f92,f153])).

fof(f153,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3,X0) ),
    inference(subsumption_resolution,[],[f152,f61])).

fof(f152,plain,(
    ! [X0] :
      ( k9_relat_1(sK3,X0) = k7_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3,X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f150,f29])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | k9_relat_1(X0,X1) = k7_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f113,f55])).

fof(f113,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X2)
      | k7_relset_1(k1_relat_1(X1),X2,X1,X3) = k9_relat_1(X1,X3)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f49,f40])).

fof(f92,plain,(
    ! [X6,X4,X7,X5] :
      ( r1_tarski(k7_relset_1(X5,X6,X4,X7),X6)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f48,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 12:10:00 EST 2020
% 0.14/0.36  % CPUTime    : 
% 1.44/0.57  % (7459)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.44/0.57  % (7457)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.58  % (7467)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.44/0.58  % (7467)Refutation not found, incomplete strategy% (7467)------------------------------
% 1.44/0.58  % (7467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.58  % (7467)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.58  
% 1.44/0.58  % (7467)Memory used [KB]: 10618
% 1.44/0.58  % (7467)Time elapsed: 0.130 s
% 1.44/0.58  % (7467)------------------------------
% 1.44/0.58  % (7467)------------------------------
% 1.44/0.58  % (7473)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.44/0.58  % (7457)Refutation found. Thanks to Tanya!
% 1.44/0.58  % SZS status Theorem for theBenchmark
% 1.44/0.58  % SZS output start Proof for theBenchmark
% 1.44/0.58  fof(f217,plain,(
% 1.44/0.58    $false),
% 1.44/0.58    inference(avatar_sat_refutation,[],[f176,f210,f216])).
% 1.44/0.58  fof(f216,plain,(
% 1.44/0.58    ~spl4_11),
% 1.44/0.58    inference(avatar_contradiction_clause,[],[f213])).
% 1.44/0.58  fof(f213,plain,(
% 1.44/0.58    $false | ~spl4_11),
% 1.44/0.58    inference(resolution,[],[f175,f140])).
% 1.44/0.58  fof(f140,plain,(
% 1.44/0.58    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 1.44/0.58    inference(backward_demodulation,[],[f116,f139])).
% 1.44/0.58  fof(f139,plain,(
% 1.44/0.58    k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)),
% 1.44/0.58    inference(forward_demodulation,[],[f138,f87])).
% 1.44/0.58  fof(f87,plain,(
% 1.44/0.58    k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3) = k2_relat_1(sK3)),
% 1.44/0.58    inference(resolution,[],[f46,f52])).
% 1.44/0.58  fof(f52,plain,(
% 1.44/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 1.44/0.58    inference(definition_unfolding,[],[f31,f50])).
% 1.44/0.58  fof(f50,plain,(
% 1.44/0.58    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.44/0.58    inference(definition_unfolding,[],[f34,f37])).
% 1.44/0.58  fof(f37,plain,(
% 1.44/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f3])).
% 1.44/0.58  fof(f3,axiom,(
% 1.44/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.44/0.58  fof(f34,plain,(
% 1.44/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f2])).
% 1.44/0.58  fof(f2,axiom,(
% 1.44/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.44/0.58  fof(f31,plain,(
% 1.44/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.44/0.58    inference(cnf_transformation,[],[f25])).
% 1.44/0.58  fof(f25,plain,(
% 1.44/0.58    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3)),
% 1.44/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f24])).
% 1.44/0.58  fof(f24,plain,(
% 1.44/0.58    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3))),
% 1.44/0.58    introduced(choice_axiom,[])).
% 1.44/0.58  fof(f15,plain,(
% 1.44/0.58    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 1.44/0.58    inference(flattening,[],[f14])).
% 1.44/0.58  fof(f14,plain,(
% 1.44/0.58    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 1.44/0.58    inference(ennf_transformation,[],[f13])).
% 1.44/0.58  fof(f13,negated_conjecture,(
% 1.44/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.44/0.58    inference(negated_conjecture,[],[f12])).
% 1.44/0.58  fof(f12,conjecture,(
% 1.44/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 1.44/0.58  fof(f46,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f19])).
% 1.44/0.58  fof(f19,plain,(
% 1.44/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.58    inference(ennf_transformation,[],[f8])).
% 1.44/0.58  fof(f8,axiom,(
% 1.44/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.44/0.58  fof(f138,plain,(
% 1.44/0.58    k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3)),
% 1.44/0.58    inference(subsumption_resolution,[],[f137,f29])).
% 1.44/0.58  fof(f29,plain,(
% 1.44/0.58    v1_funct_1(sK3)),
% 1.44/0.58    inference(cnf_transformation,[],[f25])).
% 1.44/0.58  fof(f137,plain,(
% 1.44/0.58    k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3) | ~v1_funct_1(sK3)),
% 1.44/0.58    inference(subsumption_resolution,[],[f136,f53])).
% 1.44/0.58  fof(f53,plain,(
% 1.44/0.58    v1_funct_2(sK3,k1_enumset1(sK0,sK0,sK0),sK1)),
% 1.44/0.58    inference(definition_unfolding,[],[f30,f50])).
% 1.44/0.58  fof(f30,plain,(
% 1.44/0.58    v1_funct_2(sK3,k1_tarski(sK0),sK1)),
% 1.44/0.58    inference(cnf_transformation,[],[f25])).
% 1.44/0.58  fof(f136,plain,(
% 1.44/0.58    k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3) | ~v1_funct_2(sK3,k1_enumset1(sK0,sK0,sK0),sK1) | ~v1_funct_1(sK3)),
% 1.44/0.58    inference(subsumption_resolution,[],[f135,f32])).
% 1.44/0.58  fof(f32,plain,(
% 1.44/0.58    k1_xboole_0 != sK1),
% 1.44/0.58    inference(cnf_transformation,[],[f25])).
% 1.44/0.58  fof(f135,plain,(
% 1.44/0.58    k1_xboole_0 = sK1 | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3) | ~v1_funct_2(sK3,k1_enumset1(sK0,sK0,sK0),sK1) | ~v1_funct_1(sK3)),
% 1.44/0.58    inference(resolution,[],[f54,f52])).
% 1.44/0.58  fof(f54,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(X0,X0,X0),X1))) | k1_xboole_0 = X1 | k2_relset_1(k1_enumset1(X0,X0,X0),X1,X2) = k1_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0)) | ~v1_funct_2(X2,k1_enumset1(X0,X0,X0),X1) | ~v1_funct_1(X2)) )),
% 1.44/0.58    inference(definition_unfolding,[],[f47,f50,f50,f50,f50])).
% 1.44/0.58  fof(f47,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) | ~v1_funct_2(X2,k1_tarski(X0),X1) | ~v1_funct_1(X2)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f21])).
% 1.44/0.58  fof(f21,plain,(
% 1.44/0.58    ! [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) | ~v1_funct_2(X2,k1_tarski(X0),X1) | ~v1_funct_1(X2))),
% 1.44/0.58    inference(flattening,[],[f20])).
% 1.44/0.58  fof(f20,plain,(
% 1.44/0.58    ! [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) | k1_xboole_0 = X1) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) | ~v1_funct_2(X2,k1_tarski(X0),X1) | ~v1_funct_1(X2)))),
% 1.44/0.58    inference(ennf_transformation,[],[f11])).
% 1.44/0.58  fof(f11,axiom,(
% 1.44/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).
% 1.44/0.58  fof(f116,plain,(
% 1.44/0.58    ~r1_tarski(k9_relat_1(sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.44/0.58    inference(backward_demodulation,[],[f51,f112])).
% 1.44/0.58  fof(f112,plain,(
% 1.44/0.58    ( ! [X0] : (k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.44/0.58    inference(resolution,[],[f49,f52])).
% 1.44/0.58  fof(f49,plain,(
% 1.44/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f23])).
% 1.44/0.58  fof(f23,plain,(
% 1.44/0.58    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.58    inference(ennf_transformation,[],[f9])).
% 1.44/0.58  fof(f9,axiom,(
% 1.44/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.44/0.58  fof(f51,plain,(
% 1.44/0.58    ~r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.44/0.58    inference(definition_unfolding,[],[f33,f50,f50])).
% 1.44/0.58  fof(f33,plain,(
% 1.44/0.58    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.44/0.58    inference(cnf_transformation,[],[f25])).
% 1.44/0.58  fof(f175,plain,(
% 1.44/0.58    ( ! [X1] : (r1_tarski(k9_relat_1(sK3,X1),k2_relat_1(sK3))) ) | ~spl4_11),
% 1.44/0.58    inference(avatar_component_clause,[],[f174])).
% 1.44/0.58  fof(f174,plain,(
% 1.44/0.58    spl4_11 <=> ! [X1] : r1_tarski(k9_relat_1(sK3,X1),k2_relat_1(sK3))),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.44/0.58  fof(f210,plain,(
% 1.44/0.58    spl4_10),
% 1.44/0.58    inference(avatar_contradiction_clause,[],[f209])).
% 1.44/0.58  fof(f209,plain,(
% 1.44/0.58    $false | spl4_10),
% 1.44/0.58    inference(subsumption_resolution,[],[f208,f61])).
% 1.44/0.58  fof(f61,plain,(
% 1.44/0.58    v1_relat_1(sK3)),
% 1.44/0.58    inference(subsumption_resolution,[],[f59,f36])).
% 1.44/0.58  fof(f36,plain,(
% 1.44/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.44/0.58    inference(cnf_transformation,[],[f6])).
% 1.44/0.58  fof(f6,axiom,(
% 1.44/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.44/0.58  fof(f59,plain,(
% 1.44/0.58    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))),
% 1.44/0.58    inference(resolution,[],[f35,f52])).
% 1.44/0.58  fof(f35,plain,(
% 1.44/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f16])).
% 1.44/0.58  fof(f16,plain,(
% 1.44/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.44/0.58    inference(ennf_transformation,[],[f5])).
% 1.44/0.58  fof(f5,axiom,(
% 1.44/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.44/0.58  fof(f208,plain,(
% 1.44/0.58    ~v1_relat_1(sK3) | spl4_10),
% 1.44/0.58    inference(subsumption_resolution,[],[f207,f29])).
% 1.44/0.58  fof(f207,plain,(
% 1.44/0.58    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_10),
% 1.44/0.58    inference(subsumption_resolution,[],[f205,f55])).
% 1.44/0.58  fof(f55,plain,(
% 1.44/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.44/0.58    inference(equality_resolution,[],[f42])).
% 1.44/0.58  fof(f42,plain,(
% 1.44/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.44/0.58    inference(cnf_transformation,[],[f27])).
% 1.44/0.58  fof(f27,plain,(
% 1.44/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.58    inference(flattening,[],[f26])).
% 1.44/0.58  fof(f26,plain,(
% 1.44/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.58    inference(nnf_transformation,[],[f1])).
% 1.44/0.58  fof(f1,axiom,(
% 1.44/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.44/0.58  fof(f205,plain,(
% 1.44/0.58    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_10),
% 1.44/0.58    inference(resolution,[],[f172,f40])).
% 1.44/0.58  fof(f40,plain,(
% 1.44/0.58    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f18])).
% 1.44/0.58  fof(f18,plain,(
% 1.44/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.44/0.58    inference(flattening,[],[f17])).
% 1.44/0.58  fof(f17,plain,(
% 1.44/0.58    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.44/0.58    inference(ennf_transformation,[],[f10])).
% 1.44/0.58  fof(f10,axiom,(
% 1.44/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 1.44/0.58  fof(f172,plain,(
% 1.44/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | spl4_10),
% 1.44/0.58    inference(avatar_component_clause,[],[f170])).
% 1.44/0.58  fof(f170,plain,(
% 1.44/0.58    spl4_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.44/0.58  fof(f176,plain,(
% 1.44/0.58    ~spl4_10 | spl4_11),
% 1.44/0.58    inference(avatar_split_clause,[],[f155,f174,f170])).
% 1.44/0.58  fof(f155,plain,(
% 1.44/0.58    ( ! [X1] : (r1_tarski(k9_relat_1(sK3,X1),k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))) )),
% 1.44/0.58    inference(superposition,[],[f92,f153])).
% 1.44/0.58  fof(f153,plain,(
% 1.44/0.58    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3,X0)) )),
% 1.44/0.58    inference(subsumption_resolution,[],[f152,f61])).
% 1.44/0.58  fof(f152,plain,(
% 1.44/0.58    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3,X0) | ~v1_relat_1(sK3)) )),
% 1.44/0.58    inference(resolution,[],[f150,f29])).
% 1.44/0.58  fof(f150,plain,(
% 1.44/0.58    ( ! [X0,X1] : (~v1_funct_1(X0) | k9_relat_1(X0,X1) = k7_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0,X1) | ~v1_relat_1(X0)) )),
% 1.44/0.58    inference(resolution,[],[f113,f55])).
% 1.44/0.58  fof(f113,plain,(
% 1.44/0.58    ( ! [X2,X3,X1] : (~r1_tarski(k2_relat_1(X1),X2) | k7_relset_1(k1_relat_1(X1),X2,X1,X3) = k9_relat_1(X1,X3) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.44/0.58    inference(resolution,[],[f49,f40])).
% 1.44/0.58  fof(f92,plain,(
% 1.44/0.58    ( ! [X6,X4,X7,X5] : (r1_tarski(k7_relset_1(X5,X6,X4,X7),X6) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 1.44/0.58    inference(resolution,[],[f48,f44])).
% 1.44/0.58  fof(f44,plain,(
% 1.44/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f28])).
% 1.44/0.58  fof(f28,plain,(
% 1.44/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.44/0.58    inference(nnf_transformation,[],[f4])).
% 1.44/0.58  fof(f4,axiom,(
% 1.44/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.44/0.58  fof(f48,plain,(
% 1.44/0.58    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.58    inference(cnf_transformation,[],[f22])).
% 1.44/0.58  fof(f22,plain,(
% 1.44/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.58    inference(ennf_transformation,[],[f7])).
% 1.44/0.58  fof(f7,axiom,(
% 1.44/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 1.44/0.58  % SZS output end Proof for theBenchmark
% 1.44/0.58  % (7457)------------------------------
% 1.44/0.58  % (7457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.58  % (7457)Termination reason: Refutation
% 1.44/0.58  
% 1.44/0.58  % (7457)Memory used [KB]: 10874
% 1.44/0.58  % (7457)Time elapsed: 0.138 s
% 1.44/0.58  % (7457)------------------------------
% 1.44/0.58  % (7457)------------------------------
% 1.44/0.58  % (7450)Success in time 0.2 s
%------------------------------------------------------------------------------
