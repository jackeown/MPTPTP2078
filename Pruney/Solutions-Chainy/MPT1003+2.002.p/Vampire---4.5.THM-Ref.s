%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:38 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 370 expanded)
%              Number of leaves         :   20 (  97 expanded)
%              Depth                    :   16
%              Number of atoms          :  333 (1507 expanded)
%              Number of equality atoms :  114 ( 568 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f788,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f589,f652,f655,f678,f787])).

fof(f787,plain,
    ( ~ spl7_2
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f786])).

fof(f786,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f781,f100])).

fof(f100,plain,(
    ! [X1] : ~ sP1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f781,plain,
    ( sP1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(backward_demodulation,[],[f780,f110])).

fof(f110,plain,
    ( k1_xboole_0 = sK4
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f780,plain,
    ( sP1(sK4,k1_xboole_0)
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f647,f653])).

fof(f653,plain,
    ( k1_xboole_0 = sK5
    | ~ spl7_9 ),
    inference(resolution,[],[f647,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f647,plain,
    ( sP1(sK4,sK5)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f645])).

fof(f645,plain,
    ( spl7_9
  <=> sP1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f678,plain,
    ( ~ spl7_7
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f677])).

fof(f677,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f676,f669])).

fof(f669,plain,
    ( sK4 = k10_relat_1(sK6,k2_relat_1(sK6))
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f607,f651])).

fof(f651,plain,
    ( sK4 = k1_relat_1(sK6)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f649])).

fof(f649,plain,
    ( spl7_10
  <=> sK4 = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f607,plain,
    ( k1_relat_1(sK6) = k10_relat_1(sK6,k2_relat_1(sK6))
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f606,f231])).

fof(f231,plain,(
    k1_relat_1(sK6) = k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) ),
    inference(subsumption_resolution,[],[f230,f118])).

fof(f118,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f76,f58])).

fof(f58,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( sK4 != k8_relset_1(sK4,sK5,sK6,k7_relset_1(sK4,sK5,sK6,sK4))
    & ( k1_xboole_0 = sK4
      | k1_xboole_0 != sK5 )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f21,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK4 != k8_relset_1(sK4,sK5,sK6,k7_relset_1(sK4,sK5,sK6,sK4))
      & ( k1_xboole_0 = sK4
        | k1_xboole_0 != sK5 )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_2)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f230,plain,
    ( k1_relat_1(sK6) = k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f211,f56])).

fof(f56,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f211,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) = k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f207,f182])).

fof(f182,plain,(
    ! [X0] :
      ( sP0(k2_relat_1(X0),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f67,f93])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | sP0(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f26,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f207,plain,(
    ! [X2,X3] :
      ( ~ sP0(X3,X2)
      | k1_relat_1(X2) = k1_relset_1(k1_relat_1(X2),X3,X2) ) ),
    inference(resolution,[],[f77,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f606,plain,
    ( k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) = k10_relat_1(sK6,k2_relat_1(sK6))
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f599,f516])).

fof(f516,plain,(
    ! [X0] : k10_relat_1(sK6,X0) = k8_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,X0) ),
    inference(subsumption_resolution,[],[f515,f118])).

fof(f515,plain,(
    ! [X0] :
      ( k10_relat_1(sK6,X0) = k8_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,X0)
      | ~ v1_relat_1(sK6) ) ),
    inference(resolution,[],[f305,f56])).

fof(f305,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | k10_relat_1(X0,X1) = k8_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f297,f182])).

fof(f297,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0)
      | k8_relset_1(k1_relat_1(X0),X1,X0,X2) = k10_relat_1(X0,X2) ) ),
    inference(resolution,[],[f91,f66])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f599,plain,
    ( k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) = k8_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k2_relat_1(sK6))
    | ~ spl7_7 ),
    inference(resolution,[],[f578,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f578,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6))))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f577])).

fof(f577,plain,
    ( spl7_7
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f676,plain,
    ( sK4 != k10_relat_1(sK6,k2_relat_1(sK6))
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f318,f670])).

fof(f670,plain,
    ( k2_relat_1(sK6) = k9_relat_1(sK6,sK4)
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f608,f651])).

fof(f608,plain,
    ( k2_relat_1(sK6) = k9_relat_1(sK6,k1_relat_1(sK6))
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f296,f607])).

fof(f296,plain,(
    k2_relat_1(sK6) = k9_relat_1(sK6,k10_relat_1(sK6,k2_relat_1(sK6))) ),
    inference(subsumption_resolution,[],[f295,f118])).

fof(f295,plain,
    ( k2_relat_1(sK6) = k9_relat_1(sK6,k10_relat_1(sK6,k2_relat_1(sK6)))
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f290,f56])).

fof(f290,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k2_relat_1(X0) = k9_relat_1(X0,k10_relat_1(X0,k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f63,f93])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f318,plain,(
    sK4 != k10_relat_1(sK6,k9_relat_1(sK6,sK4)) ),
    inference(backward_demodulation,[],[f304,f315])).

fof(f315,plain,(
    ! [X16] : k7_relset_1(sK4,sK5,sK6,X16) = k9_relat_1(sK6,X16) ),
    inference(resolution,[],[f92,f58])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f304,plain,(
    sK4 != k10_relat_1(sK6,k7_relset_1(sK4,sK5,sK6,sK4)) ),
    inference(superposition,[],[f60,f301])).

fof(f301,plain,(
    ! [X16] : k8_relset_1(sK4,sK5,sK6,X16) = k10_relat_1(sK6,X16) ),
    inference(resolution,[],[f91,f58])).

fof(f60,plain,(
    sK4 != k8_relset_1(sK4,sK5,sK6,k7_relset_1(sK4,sK5,sK6,sK4)) ),
    inference(cnf_transformation,[],[f44])).

fof(f655,plain,
    ( spl7_1
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f654])).

fof(f654,plain,
    ( $false
    | spl7_1
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f653,f106])).

fof(f106,plain,
    ( k1_xboole_0 != sK5
    | spl7_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f652,plain,
    ( spl7_9
    | spl7_10 ),
    inference(avatar_split_clause,[],[f643,f649,f645])).

fof(f643,plain,
    ( sK4 = k1_relat_1(sK6)
    | sP1(sK4,sK5) ),
    inference(forward_demodulation,[],[f642,f206])).

fof(f206,plain,(
    k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(resolution,[],[f77,f58])).

fof(f642,plain,
    ( sP1(sK4,sK5)
    | sK4 = k1_relset_1(sK4,sK5,sK6) ),
    inference(subsumption_resolution,[],[f636,f57])).

fof(f57,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f636,plain,
    ( ~ v1_funct_2(sK6,sK4,sK5)
    | sP1(sK4,sK5)
    | sK4 = k1_relset_1(sK4,sK5,sK6) ),
    inference(resolution,[],[f82,f154])).

fof(f154,plain,(
    sP2(sK4,sK6,sK5) ),
    inference(resolution,[],[f86,f58])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f31,f41,f40,f39])).

fof(f40,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f589,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f588])).

fof(f588,plain,
    ( $false
    | spl7_7 ),
    inference(subsumption_resolution,[],[f587,f118])).

fof(f587,plain,
    ( ~ v1_relat_1(sK6)
    | spl7_7 ),
    inference(subsumption_resolution,[],[f586,f56])).

fof(f586,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl7_7 ),
    inference(resolution,[],[f584,f182])).

fof(f584,plain,
    ( ~ sP0(k2_relat_1(sK6),sK6)
    | spl7_7 ),
    inference(resolution,[],[f579,f66])).

fof(f579,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6))))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f577])).

fof(f111,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f59,f108,f104])).

fof(f59,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (31087)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.47  % (31087)Refutation not found, incomplete strategy% (31087)------------------------------
% 0.20/0.47  % (31087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (31087)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (31087)Memory used [KB]: 10618
% 0.20/0.47  % (31087)Time elapsed: 0.076 s
% 0.20/0.47  % (31087)------------------------------
% 0.20/0.47  % (31087)------------------------------
% 0.20/0.48  % (31104)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.48  % (31083)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.48  % (31103)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.48  % (31081)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.48  % (31082)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (31095)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (31094)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (31091)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (31085)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (31090)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (31096)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.50  % (31097)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.50  % (31105)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.50  % (31093)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (31098)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (31082)Refutation not found, incomplete strategy% (31082)------------------------------
% 0.20/0.51  % (31082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31082)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (31082)Memory used [KB]: 10746
% 0.20/0.51  % (31082)Time elapsed: 0.076 s
% 0.20/0.51  % (31082)------------------------------
% 0.20/0.51  % (31082)------------------------------
% 0.20/0.51  % (31086)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (31106)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.51  % (31086)Refutation not found, incomplete strategy% (31086)------------------------------
% 0.20/0.51  % (31086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31086)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (31086)Memory used [KB]: 6140
% 0.20/0.51  % (31086)Time elapsed: 0.097 s
% 0.20/0.51  % (31086)------------------------------
% 0.20/0.51  % (31086)------------------------------
% 0.20/0.51  % (31088)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (31089)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (31084)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (31099)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (31102)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (31100)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (31092)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (31092)Refutation not found, incomplete strategy% (31092)------------------------------
% 0.20/0.52  % (31092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31092)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (31092)Memory used [KB]: 10618
% 0.20/0.52  % (31092)Time elapsed: 0.122 s
% 0.20/0.52  % (31092)------------------------------
% 0.20/0.52  % (31092)------------------------------
% 0.20/0.52  % (31101)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.31/0.54  % (31106)Refutation found. Thanks to Tanya!
% 1.31/0.54  % SZS status Theorem for theBenchmark
% 1.44/0.55  % SZS output start Proof for theBenchmark
% 1.44/0.56  fof(f788,plain,(
% 1.44/0.56    $false),
% 1.44/0.56    inference(avatar_sat_refutation,[],[f111,f589,f652,f655,f678,f787])).
% 1.44/0.56  fof(f787,plain,(
% 1.44/0.56    ~spl7_2 | ~spl7_9),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f786])).
% 1.44/0.56  fof(f786,plain,(
% 1.44/0.56    $false | (~spl7_2 | ~spl7_9)),
% 1.44/0.56    inference(subsumption_resolution,[],[f781,f100])).
% 1.44/0.56  fof(f100,plain,(
% 1.44/0.56    ( ! [X1] : (~sP1(k1_xboole_0,X1)) )),
% 1.44/0.56    inference(equality_resolution,[],[f85])).
% 1.44/0.56  fof(f85,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP1(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f55])).
% 1.44/0.56  fof(f55,plain,(
% 1.44/0.56    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 1.44/0.56    inference(nnf_transformation,[],[f39])).
% 1.44/0.56  fof(f39,plain,(
% 1.44/0.56    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 1.44/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.44/0.56  fof(f781,plain,(
% 1.44/0.56    sP1(k1_xboole_0,k1_xboole_0) | (~spl7_2 | ~spl7_9)),
% 1.44/0.56    inference(backward_demodulation,[],[f780,f110])).
% 1.44/0.56  fof(f110,plain,(
% 1.44/0.56    k1_xboole_0 = sK4 | ~spl7_2),
% 1.44/0.56    inference(avatar_component_clause,[],[f108])).
% 1.44/0.56  fof(f108,plain,(
% 1.44/0.56    spl7_2 <=> k1_xboole_0 = sK4),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.44/0.56  fof(f780,plain,(
% 1.44/0.56    sP1(sK4,k1_xboole_0) | ~spl7_9),
% 1.44/0.56    inference(forward_demodulation,[],[f647,f653])).
% 1.44/0.56  fof(f653,plain,(
% 1.44/0.56    k1_xboole_0 = sK5 | ~spl7_9),
% 1.44/0.56    inference(resolution,[],[f647,f84])).
% 1.44/0.56  fof(f84,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~sP1(X0,X1) | k1_xboole_0 = X1) )),
% 1.44/0.56    inference(cnf_transformation,[],[f55])).
% 1.44/0.56  fof(f647,plain,(
% 1.44/0.56    sP1(sK4,sK5) | ~spl7_9),
% 1.44/0.56    inference(avatar_component_clause,[],[f645])).
% 1.44/0.56  fof(f645,plain,(
% 1.44/0.56    spl7_9 <=> sP1(sK4,sK5)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.44/0.56  fof(f678,plain,(
% 1.44/0.56    ~spl7_7 | ~spl7_10),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f677])).
% 1.44/0.56  fof(f677,plain,(
% 1.44/0.56    $false | (~spl7_7 | ~spl7_10)),
% 1.44/0.56    inference(subsumption_resolution,[],[f676,f669])).
% 1.44/0.56  fof(f669,plain,(
% 1.44/0.56    sK4 = k10_relat_1(sK6,k2_relat_1(sK6)) | (~spl7_7 | ~spl7_10)),
% 1.44/0.56    inference(backward_demodulation,[],[f607,f651])).
% 1.44/0.56  fof(f651,plain,(
% 1.44/0.56    sK4 = k1_relat_1(sK6) | ~spl7_10),
% 1.44/0.56    inference(avatar_component_clause,[],[f649])).
% 1.44/0.56  fof(f649,plain,(
% 1.44/0.56    spl7_10 <=> sK4 = k1_relat_1(sK6)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.44/0.56  fof(f607,plain,(
% 1.44/0.56    k1_relat_1(sK6) = k10_relat_1(sK6,k2_relat_1(sK6)) | ~spl7_7),
% 1.44/0.56    inference(forward_demodulation,[],[f606,f231])).
% 1.44/0.56  fof(f231,plain,(
% 1.44/0.56    k1_relat_1(sK6) = k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6)),
% 1.44/0.56    inference(subsumption_resolution,[],[f230,f118])).
% 1.44/0.56  fof(f118,plain,(
% 1.44/0.56    v1_relat_1(sK6)),
% 1.44/0.56    inference(resolution,[],[f76,f58])).
% 1.44/0.56  fof(f58,plain,(
% 1.44/0.56    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 1.44/0.56    inference(cnf_transformation,[],[f44])).
% 1.44/0.56  fof(f44,plain,(
% 1.44/0.56    sK4 != k8_relset_1(sK4,sK5,sK6,k7_relset_1(sK4,sK5,sK6,sK4)) & (k1_xboole_0 = sK4 | k1_xboole_0 != sK5) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f21,f43])).
% 1.44/0.56  fof(f43,plain,(
% 1.44/0.56    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK4 != k8_relset_1(sK4,sK5,sK6,k7_relset_1(sK4,sK5,sK6,sK4)) & (k1_xboole_0 = sK4 | k1_xboole_0 != sK5) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f21,plain,(
% 1.44/0.56    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.44/0.56    inference(flattening,[],[f20])).
% 1.44/0.56  fof(f20,plain,(
% 1.44/0.56    ? [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.44/0.56    inference(ennf_transformation,[],[f18])).
% 1.44/0.56  fof(f18,negated_conjecture,(
% 1.44/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 1.44/0.56    inference(negated_conjecture,[],[f17])).
% 1.44/0.56  fof(f17,conjecture,(
% 1.44/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_2)).
% 1.44/0.56  fof(f76,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f27])).
% 1.44/0.56  fof(f27,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(ennf_transformation,[],[f8])).
% 1.44/0.56  fof(f8,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.44/0.56  fof(f230,plain,(
% 1.44/0.56    k1_relat_1(sK6) = k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) | ~v1_relat_1(sK6)),
% 1.44/0.56    inference(resolution,[],[f211,f56])).
% 1.44/0.56  fof(f56,plain,(
% 1.44/0.56    v1_funct_1(sK6)),
% 1.44/0.56    inference(cnf_transformation,[],[f44])).
% 1.44/0.56  fof(f211,plain,(
% 1.44/0.56    ( ! [X0] : (~v1_funct_1(X0) | k1_relat_1(X0) = k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) | ~v1_relat_1(X0)) )),
% 1.44/0.56    inference(resolution,[],[f207,f182])).
% 1.44/0.56  fof(f182,plain,(
% 1.44/0.56    ( ! [X0] : (sP0(k2_relat_1(X0),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.56    inference(resolution,[],[f67,f93])).
% 1.44/0.56  fof(f93,plain,(
% 1.44/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.44/0.56    inference(equality_resolution,[],[f69])).
% 1.44/0.56  fof(f69,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.44/0.56    inference(cnf_transformation,[],[f47])).
% 1.44/0.56  fof(f47,plain,(
% 1.44/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.56    inference(flattening,[],[f46])).
% 1.44/0.56  fof(f46,plain,(
% 1.44/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.56    inference(nnf_transformation,[],[f1])).
% 1.44/0.56  fof(f1,axiom,(
% 1.44/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.44/0.56  fof(f67,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | sP0(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f38])).
% 1.44/0.56  fof(f38,plain,(
% 1.44/0.56    ! [X0,X1] : (sP0(X0,X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.44/0.56    inference(definition_folding,[],[f26,f37])).
% 1.44/0.56  fof(f37,plain,(
% 1.44/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP0(X0,X1))),
% 1.44/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.44/0.56  fof(f26,plain,(
% 1.44/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.44/0.56    inference(flattening,[],[f25])).
% 1.44/0.56  fof(f25,plain,(
% 1.44/0.56    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.44/0.56    inference(ennf_transformation,[],[f16])).
% 1.44/0.56  fof(f16,axiom,(
% 1.44/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 1.44/0.56  fof(f207,plain,(
% 1.44/0.56    ( ! [X2,X3] : (~sP0(X3,X2) | k1_relat_1(X2) = k1_relset_1(k1_relat_1(X2),X3,X2)) )),
% 1.44/0.56    inference(resolution,[],[f77,f66])).
% 1.44/0.56  fof(f66,plain,(
% 1.44/0.56    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~sP0(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f45])).
% 1.44/0.56  fof(f45,plain,(
% 1.44/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP0(X0,X1))),
% 1.44/0.56    inference(nnf_transformation,[],[f37])).
% 1.44/0.56  fof(f77,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f28])).
% 1.44/0.56  fof(f28,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(ennf_transformation,[],[f10])).
% 1.44/0.56  fof(f10,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.44/0.56  fof(f606,plain,(
% 1.44/0.56    k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) = k10_relat_1(sK6,k2_relat_1(sK6)) | ~spl7_7),
% 1.44/0.56    inference(forward_demodulation,[],[f599,f516])).
% 1.44/0.56  fof(f516,plain,(
% 1.44/0.56    ( ! [X0] : (k10_relat_1(sK6,X0) = k8_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,X0)) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f515,f118])).
% 1.44/0.56  fof(f515,plain,(
% 1.44/0.56    ( ! [X0] : (k10_relat_1(sK6,X0) = k8_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,X0) | ~v1_relat_1(sK6)) )),
% 1.44/0.56    inference(resolution,[],[f305,f56])).
% 1.44/0.56  fof(f305,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~v1_funct_1(X0) | k10_relat_1(X0,X1) = k8_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0,X1) | ~v1_relat_1(X0)) )),
% 1.44/0.56    inference(resolution,[],[f297,f182])).
% 1.44/0.56  fof(f297,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~sP0(X1,X0) | k8_relset_1(k1_relat_1(X0),X1,X0,X2) = k10_relat_1(X0,X2)) )),
% 1.44/0.56    inference(resolution,[],[f91,f66])).
% 1.44/0.56  fof(f91,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f35])).
% 1.44/0.56  fof(f35,plain,(
% 1.44/0.56    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(ennf_transformation,[],[f12])).
% 1.44/0.56  fof(f12,axiom,(
% 1.44/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.44/0.56  fof(f599,plain,(
% 1.44/0.56    k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) = k8_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k2_relat_1(sK6)) | ~spl7_7),
% 1.44/0.56    inference(resolution,[],[f578,f79])).
% 1.44/0.56  fof(f79,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f29])).
% 1.44/0.56  fof(f29,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(ennf_transformation,[],[f13])).
% 1.44/0.56  fof(f13,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 1.44/0.56  fof(f578,plain,(
% 1.44/0.56    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6)))) | ~spl7_7),
% 1.44/0.56    inference(avatar_component_clause,[],[f577])).
% 1.44/0.56  fof(f577,plain,(
% 1.44/0.56    spl7_7 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6))))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.44/0.56  fof(f676,plain,(
% 1.44/0.56    sK4 != k10_relat_1(sK6,k2_relat_1(sK6)) | (~spl7_7 | ~spl7_10)),
% 1.44/0.56    inference(backward_demodulation,[],[f318,f670])).
% 1.44/0.56  fof(f670,plain,(
% 1.44/0.56    k2_relat_1(sK6) = k9_relat_1(sK6,sK4) | (~spl7_7 | ~spl7_10)),
% 1.44/0.56    inference(backward_demodulation,[],[f608,f651])).
% 1.44/0.56  fof(f608,plain,(
% 1.44/0.56    k2_relat_1(sK6) = k9_relat_1(sK6,k1_relat_1(sK6)) | ~spl7_7),
% 1.44/0.56    inference(backward_demodulation,[],[f296,f607])).
% 1.44/0.56  fof(f296,plain,(
% 1.44/0.56    k2_relat_1(sK6) = k9_relat_1(sK6,k10_relat_1(sK6,k2_relat_1(sK6)))),
% 1.44/0.56    inference(subsumption_resolution,[],[f295,f118])).
% 1.44/0.56  fof(f295,plain,(
% 1.44/0.56    k2_relat_1(sK6) = k9_relat_1(sK6,k10_relat_1(sK6,k2_relat_1(sK6))) | ~v1_relat_1(sK6)),
% 1.44/0.56    inference(resolution,[],[f290,f56])).
% 1.44/0.56  fof(f290,plain,(
% 1.44/0.56    ( ! [X0] : (~v1_funct_1(X0) | k2_relat_1(X0) = k9_relat_1(X0,k10_relat_1(X0,k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.44/0.56    inference(resolution,[],[f63,f93])).
% 1.44/0.56  fof(f63,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f24])).
% 1.44/0.56  fof(f24,plain,(
% 1.44/0.56    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.44/0.56    inference(flattening,[],[f23])).
% 1.44/0.56  fof(f23,plain,(
% 1.44/0.56    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.44/0.56    inference(ennf_transformation,[],[f7])).
% 1.44/0.56  fof(f7,axiom,(
% 1.44/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 1.44/0.56  fof(f318,plain,(
% 1.44/0.56    sK4 != k10_relat_1(sK6,k9_relat_1(sK6,sK4))),
% 1.44/0.56    inference(backward_demodulation,[],[f304,f315])).
% 1.44/0.56  fof(f315,plain,(
% 1.44/0.56    ( ! [X16] : (k7_relset_1(sK4,sK5,sK6,X16) = k9_relat_1(sK6,X16)) )),
% 1.44/0.56    inference(resolution,[],[f92,f58])).
% 1.44/0.56  fof(f92,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f36])).
% 1.44/0.56  fof(f36,plain,(
% 1.44/0.56    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(ennf_transformation,[],[f11])).
% 1.44/0.56  fof(f11,axiom,(
% 1.44/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.44/0.56  fof(f304,plain,(
% 1.44/0.56    sK4 != k10_relat_1(sK6,k7_relset_1(sK4,sK5,sK6,sK4))),
% 1.44/0.56    inference(superposition,[],[f60,f301])).
% 1.44/0.56  fof(f301,plain,(
% 1.44/0.56    ( ! [X16] : (k8_relset_1(sK4,sK5,sK6,X16) = k10_relat_1(sK6,X16)) )),
% 1.44/0.56    inference(resolution,[],[f91,f58])).
% 1.44/0.56  fof(f60,plain,(
% 1.44/0.56    sK4 != k8_relset_1(sK4,sK5,sK6,k7_relset_1(sK4,sK5,sK6,sK4))),
% 1.44/0.56    inference(cnf_transformation,[],[f44])).
% 1.44/0.56  fof(f655,plain,(
% 1.44/0.56    spl7_1 | ~spl7_9),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f654])).
% 1.44/0.56  fof(f654,plain,(
% 1.44/0.56    $false | (spl7_1 | ~spl7_9)),
% 1.44/0.56    inference(subsumption_resolution,[],[f653,f106])).
% 1.44/0.56  fof(f106,plain,(
% 1.44/0.56    k1_xboole_0 != sK5 | spl7_1),
% 1.44/0.56    inference(avatar_component_clause,[],[f104])).
% 1.44/0.56  fof(f104,plain,(
% 1.44/0.56    spl7_1 <=> k1_xboole_0 = sK5),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.44/0.56  fof(f652,plain,(
% 1.44/0.56    spl7_9 | spl7_10),
% 1.44/0.56    inference(avatar_split_clause,[],[f643,f649,f645])).
% 1.44/0.56  fof(f643,plain,(
% 1.44/0.56    sK4 = k1_relat_1(sK6) | sP1(sK4,sK5)),
% 1.44/0.56    inference(forward_demodulation,[],[f642,f206])).
% 1.44/0.56  fof(f206,plain,(
% 1.44/0.56    k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6)),
% 1.44/0.56    inference(resolution,[],[f77,f58])).
% 1.44/0.56  fof(f642,plain,(
% 1.44/0.56    sP1(sK4,sK5) | sK4 = k1_relset_1(sK4,sK5,sK6)),
% 1.44/0.56    inference(subsumption_resolution,[],[f636,f57])).
% 1.44/0.56  fof(f57,plain,(
% 1.44/0.56    v1_funct_2(sK6,sK4,sK5)),
% 1.44/0.56    inference(cnf_transformation,[],[f44])).
% 1.44/0.56  fof(f636,plain,(
% 1.44/0.56    ~v1_funct_2(sK6,sK4,sK5) | sP1(sK4,sK5) | sK4 = k1_relset_1(sK4,sK5,sK6)),
% 1.44/0.56    inference(resolution,[],[f82,f154])).
% 1.44/0.56  fof(f154,plain,(
% 1.44/0.56    sP2(sK4,sK6,sK5)),
% 1.44/0.56    inference(resolution,[],[f86,f58])).
% 1.44/0.56  fof(f86,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f42])).
% 1.44/0.56  fof(f42,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(definition_folding,[],[f31,f41,f40,f39])).
% 1.44/0.56  fof(f40,plain,(
% 1.44/0.56    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 1.44/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.44/0.56  fof(f41,plain,(
% 1.44/0.56    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 1.44/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.44/0.56  fof(f31,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(flattening,[],[f30])).
% 1.44/0.56  fof(f30,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(ennf_transformation,[],[f14])).
% 1.44/0.56  fof(f14,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.44/0.56  fof(f82,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | k1_relset_1(X0,X2,X1) = X0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f54])).
% 1.44/0.56  fof(f54,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 1.44/0.56    inference(rectify,[],[f53])).
% 1.44/0.56  fof(f53,plain,(
% 1.44/0.56    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 1.44/0.56    inference(nnf_transformation,[],[f40])).
% 1.44/0.56  fof(f589,plain,(
% 1.44/0.56    spl7_7),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f588])).
% 1.44/0.56  fof(f588,plain,(
% 1.44/0.56    $false | spl7_7),
% 1.44/0.56    inference(subsumption_resolution,[],[f587,f118])).
% 1.44/0.56  fof(f587,plain,(
% 1.44/0.56    ~v1_relat_1(sK6) | spl7_7),
% 1.44/0.56    inference(subsumption_resolution,[],[f586,f56])).
% 1.44/0.56  fof(f586,plain,(
% 1.44/0.56    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl7_7),
% 1.44/0.56    inference(resolution,[],[f584,f182])).
% 1.44/0.56  fof(f584,plain,(
% 1.44/0.56    ~sP0(k2_relat_1(sK6),sK6) | spl7_7),
% 1.44/0.56    inference(resolution,[],[f579,f66])).
% 1.44/0.56  fof(f579,plain,(
% 1.44/0.56    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6)))) | spl7_7),
% 1.44/0.56    inference(avatar_component_clause,[],[f577])).
% 1.44/0.56  fof(f111,plain,(
% 1.44/0.56    ~spl7_1 | spl7_2),
% 1.44/0.56    inference(avatar_split_clause,[],[f59,f108,f104])).
% 1.44/0.56  fof(f59,plain,(
% 1.44/0.56    k1_xboole_0 = sK4 | k1_xboole_0 != sK5),
% 1.44/0.56    inference(cnf_transformation,[],[f44])).
% 1.44/0.56  % SZS output end Proof for theBenchmark
% 1.44/0.56  % (31106)------------------------------
% 1.44/0.56  % (31106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (31106)Termination reason: Refutation
% 1.44/0.56  
% 1.44/0.56  % (31106)Memory used [KB]: 11129
% 1.44/0.56  % (31106)Time elapsed: 0.125 s
% 1.44/0.56  % (31106)------------------------------
% 1.44/0.56  % (31106)------------------------------
% 1.44/0.57  % (31080)Success in time 0.206 s
%------------------------------------------------------------------------------
