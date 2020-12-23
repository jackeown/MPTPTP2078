%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:25 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 416 expanded)
%              Number of leaves         :   35 ( 137 expanded)
%              Depth                    :   15
%              Number of atoms          :  395 ( 941 expanded)
%              Number of equality atoms :   83 ( 291 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f641,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f137,f157,f295,f329,f352,f357,f380,f388,f464,f473,f501,f574,f640])).

fof(f640,plain,
    ( ~ spl7_21
    | ~ spl7_27 ),
    inference(avatar_contradiction_clause,[],[f639])).

fof(f639,plain,
    ( $false
    | ~ spl7_21
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f517,f575])).

fof(f575,plain,
    ( ! [X0] : v1_xboole_0(k9_relat_1(k1_xboole_0,X0))
    | ~ spl7_21
    | ~ spl7_27 ),
    inference(forward_demodulation,[],[f472,f351])).

fof(f351,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl7_21
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f472,plain,
    ( ! [X0] : v1_xboole_0(k9_relat_1(sK3,X0))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f471])).

fof(f471,plain,
    ( spl7_27
  <=> ! [X0] : v1_xboole_0(k9_relat_1(sK3,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f517,plain,
    ( ~ v1_xboole_0(k9_relat_1(k1_xboole_0,sK2))
    | ~ spl7_21 ),
    inference(backward_demodulation,[],[f165,f351])).

fof(f165,plain,(
    ~ v1_xboole_0(k9_relat_1(sK3,sK2)) ),
    inference(resolution,[],[f164,f81])).

fof(f81,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f56,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f164,plain,(
    r2_hidden(sK6(k9_relat_1(sK3,sK2),k3_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))),k9_relat_1(sK3,sK2)) ),
    inference(resolution,[],[f161,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f63,f64])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f161,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k3_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f111,f119])).

fof(f119,plain,(
    ! [X0] : k7_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f112,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f112,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f70,f110])).

fof(f110,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f74,f109])).

fof(f109,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f85,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f100,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f100,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f85,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f74,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f53])).

fof(f53,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f28])).

% (28490)Termination reason: Refutation not found, incomplete strategy

% (28490)Memory used [KB]: 10618
% (28490)Time elapsed: 0.151 s
% (28490)------------------------------
% (28490)------------------------------
fof(f28,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f111,plain,(
    ~ r1_tarski(k7_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k3_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f72,f110,f110])).

fof(f72,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f574,plain,
    ( ~ spl7_21
    | spl7_26 ),
    inference(avatar_contradiction_clause,[],[f573])).

fof(f573,plain,
    ( $false
    | ~ spl7_21
    | spl7_26 ),
    inference(subsumption_resolution,[],[f73,f540])).

fof(f540,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_21
    | spl7_26 ),
    inference(backward_demodulation,[],[f481,f351])).

fof(f481,plain,
    ( ~ v1_xboole_0(sK3)
    | spl7_26 ),
    inference(resolution,[],[f469,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f469,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK3))
    | spl7_26 ),
    inference(avatar_component_clause,[],[f468])).

fof(f468,plain,
    ( spl7_26
  <=> v1_xboole_0(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f73,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f501,plain,
    ( ~ spl7_4
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f499])).

fof(f499,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(resolution,[],[f493,f444])).

fof(f444,plain,
    ( ! [X1] : r1_tarski(k9_relat_1(sK3,X1),k2_relat_1(sK3))
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f379,f184])).

fof(f184,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3)
    | ~ spl7_4 ),
    inference(superposition,[],[f158,f159])).

fof(f159,plain,
    ( sK3 = k7_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl7_4 ),
    inference(resolution,[],[f136,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f136,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl7_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f158,plain,
    ( ! [X0] : k9_relat_1(sK3,X0) = k2_relat_1(k7_relat_1(sK3,X0))
    | ~ spl7_4 ),
    inference(resolution,[],[f136,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f379,plain,
    ( ! [X1] : r1_tarski(k9_relat_1(sK3,X1),k9_relat_1(sK3,k1_relat_1(sK3)))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl7_22
  <=> ! [X1] : r1_tarski(k9_relat_1(sK3,X1),k9_relat_1(sK3,k1_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f493,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl7_19 ),
    inference(backward_demodulation,[],[f161,f326])).

fof(f326,plain,
    ( k3_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f325])).

fof(f325,plain,
    ( spl7_19
  <=> k3_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f473,plain,
    ( ~ spl7_26
    | spl7_27
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f465,f293,f471,f468])).

fof(f293,plain,
    ( spl7_17
  <=> ! [X1,X0] :
        ( r2_hidden(X0,k2_relat_1(sK3))
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f465,plain,
    ( ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK3,X0))
        | ~ v1_xboole_0(k2_relat_1(sK3)) )
    | ~ spl7_17 ),
    inference(resolution,[],[f304,f81])).

fof(f304,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k9_relat_1(sK3,X0)),k2_relat_1(sK3))
        | v1_xboole_0(k9_relat_1(sK3,X0)) )
    | ~ spl7_17 ),
    inference(resolution,[],[f294,f82])).

fof(f82,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f294,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(X0,k2_relat_1(sK3)) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f293])).

fof(f464,plain,
    ( ~ spl7_4
    | ~ spl7_18
    | spl7_19
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f463,f199,f325,f322,f135])).

fof(f322,plain,
    ( spl7_18
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f199,plain,
    ( spl7_11
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f463,plain,
    ( k3_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_11 ),
    inference(equality_resolution,[],[f434])).

fof(f434,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != k1_relat_1(sK3)
        | k2_relat_1(X1) = k3_enumset1(k1_funct_1(X1,sK0),k1_funct_1(X1,sK0),k1_funct_1(X1,sK0),k1_funct_1(X1,sK0),k1_funct_1(X1,sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl7_11 ),
    inference(superposition,[],[f113,f200])).

fof(f200,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f199])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k3_enumset1(X0,X0,X0,X0,X0)
      | k2_relat_1(X1) = k3_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f90,f110,f110])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f388,plain,
    ( spl7_11
    | spl7_12
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f385,f152,f202,f199])).

fof(f202,plain,
    ( spl7_12
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f152,plain,
    ( spl7_7
  <=> r1_tarski(k1_relat_1(sK3),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f385,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl7_7 ),
    inference(resolution,[],[f153,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f95,f110,f110])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f153,plain,
    ( r1_tarski(k1_relat_1(sK3),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f152])).

fof(f380,plain,
    ( ~ spl7_4
    | spl7_22
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f369,f135,f378,f135])).

fof(f369,plain,
    ( ! [X1] :
        ( r1_tarski(k9_relat_1(sK3,X1),k9_relat_1(sK3,k1_relat_1(sK3)))
        | ~ v1_relat_1(sK3) )
    | ~ spl7_4 ),
    inference(superposition,[],[f185,f159])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0),X1),k9_relat_1(sK3,X0))
        | ~ v1_relat_1(k7_relat_1(sK3,X0)) )
    | ~ spl7_4 ),
    inference(superposition,[],[f86,f158])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f357,plain,
    ( ~ spl7_4
    | spl7_7 ),
    inference(avatar_split_clause,[],[f355,f152,f135])).

fof(f355,plain,
    ( r1_tarski(k1_relat_1(sK3),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f120,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f120,plain,(
    v4_relat_1(sK3,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f112,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f352,plain,
    ( ~ spl7_4
    | spl7_21
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f344,f202,f350,f135])).

fof(f344,plain,
    ( k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl7_12 ),
    inference(trivial_inequality_removal,[],[f343])).

fof(f343,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl7_12 ),
    inference(superposition,[],[f78,f203])).

fof(f203,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f202])).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f329,plain,(
    spl7_18 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | spl7_18 ),
    inference(subsumption_resolution,[],[f69,f323])).

fof(f323,plain,
    ( ~ v1_funct_1(sK3)
    | spl7_18 ),
    inference(avatar_component_clause,[],[f322])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f295,plain,
    ( ~ spl7_4
    | spl7_17
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f291,f135,f293,f135])).

fof(f291,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k2_relat_1(sK3))
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | ~ v1_relat_1(sK3) )
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f289,f184])).

fof(f289,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | ~ v1_relat_1(sK3)
        | r2_hidden(X0,k9_relat_1(sK3,k1_relat_1(sK3))) )
    | ~ spl7_4 ),
    inference(superposition,[],[f270,f159])).

fof(f270,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(k7_relat_1(sK3,X0),X2))
        | ~ v1_relat_1(k7_relat_1(sK3,X0))
        | r2_hidden(X1,k9_relat_1(sK3,X0)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f185,f92])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f157,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl7_3 ),
    inference(resolution,[],[f133,f84])).

fof(f84,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f133,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl7_3
  <=> v1_relat_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f137,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f123,f135,f132])).

fof(f123,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(resolution,[],[f112,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:50:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (28475)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (28474)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (28477)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (28471)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (28491)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (28478)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (28473)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (28480)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (28495)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (28502)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.53  % (28494)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.53  % (28483)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.53  % (28474)Refutation not found, incomplete strategy% (28474)------------------------------
% 1.35/0.53  % (28474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (28474)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (28474)Memory used [KB]: 6396
% 1.35/0.53  % (28474)Time elapsed: 0.128 s
% 1.35/0.53  % (28474)------------------------------
% 1.35/0.53  % (28474)------------------------------
% 1.35/0.53  % (28472)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.53  % (28470)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.35/0.54  % (28499)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.54  % (28501)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.54  % (28498)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.54  % (28484)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.54  % (28482)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.54  % (28500)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.54  % (28493)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.55  % (28486)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.55  % (28485)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.55  % (28496)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.47/0.55  % (28492)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.47/0.55  % (28482)Refutation not found, incomplete strategy% (28482)------------------------------
% 1.47/0.55  % (28482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (28482)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (28482)Memory used [KB]: 10746
% 1.47/0.55  % (28482)Time elapsed: 0.151 s
% 1.47/0.55  % (28482)------------------------------
% 1.47/0.55  % (28482)------------------------------
% 1.47/0.55  % (28490)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.47/0.55  % (28495)Refutation not found, incomplete strategy% (28495)------------------------------
% 1.47/0.55  % (28495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (28495)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (28495)Memory used [KB]: 10874
% 1.47/0.55  % (28495)Time elapsed: 0.130 s
% 1.47/0.55  % (28495)------------------------------
% 1.47/0.55  % (28495)------------------------------
% 1.47/0.55  % (28490)Refutation not found, incomplete strategy% (28490)------------------------------
% 1.47/0.55  % (28490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (28488)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.47/0.56  % (28479)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.47/0.56  % (28476)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.47/0.56  % (28497)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.47/0.56  % (28480)Refutation not found, incomplete strategy% (28480)------------------------------
% 1.47/0.56  % (28480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (28480)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (28480)Memory used [KB]: 10618
% 1.47/0.56  % (28480)Time elapsed: 0.141 s
% 1.47/0.56  % (28480)------------------------------
% 1.47/0.56  % (28480)------------------------------
% 1.47/0.57  % (28472)Refutation found. Thanks to Tanya!
% 1.47/0.57  % SZS status Theorem for theBenchmark
% 1.47/0.57  % SZS output start Proof for theBenchmark
% 1.47/0.57  fof(f641,plain,(
% 1.47/0.57    $false),
% 1.47/0.57    inference(avatar_sat_refutation,[],[f137,f157,f295,f329,f352,f357,f380,f388,f464,f473,f501,f574,f640])).
% 1.47/0.57  fof(f640,plain,(
% 1.47/0.57    ~spl7_21 | ~spl7_27),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f639])).
% 1.47/0.57  fof(f639,plain,(
% 1.47/0.57    $false | (~spl7_21 | ~spl7_27)),
% 1.47/0.57    inference(subsumption_resolution,[],[f517,f575])).
% 1.47/0.57  fof(f575,plain,(
% 1.47/0.57    ( ! [X0] : (v1_xboole_0(k9_relat_1(k1_xboole_0,X0))) ) | (~spl7_21 | ~spl7_27)),
% 1.47/0.57    inference(forward_demodulation,[],[f472,f351])).
% 1.47/0.57  fof(f351,plain,(
% 1.47/0.57    k1_xboole_0 = sK3 | ~spl7_21),
% 1.47/0.57    inference(avatar_component_clause,[],[f350])).
% 1.47/0.57  fof(f350,plain,(
% 1.47/0.57    spl7_21 <=> k1_xboole_0 = sK3),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 1.47/0.57  fof(f472,plain,(
% 1.47/0.57    ( ! [X0] : (v1_xboole_0(k9_relat_1(sK3,X0))) ) | ~spl7_27),
% 1.47/0.57    inference(avatar_component_clause,[],[f471])).
% 1.47/0.57  fof(f471,plain,(
% 1.47/0.57    spl7_27 <=> ! [X0] : v1_xboole_0(k9_relat_1(sK3,X0))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 1.47/0.57  fof(f517,plain,(
% 1.47/0.57    ~v1_xboole_0(k9_relat_1(k1_xboole_0,sK2)) | ~spl7_21),
% 1.47/0.57    inference(backward_demodulation,[],[f165,f351])).
% 1.47/0.57  fof(f165,plain,(
% 1.47/0.57    ~v1_xboole_0(k9_relat_1(sK3,sK2))),
% 1.47/0.57    inference(resolution,[],[f164,f81])).
% 1.47/0.57  fof(f81,plain,(
% 1.47/0.57    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f58])).
% 1.47/0.57  fof(f58,plain,(
% 1.47/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.47/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f56,f57])).
% 1.47/0.57  fof(f57,plain,(
% 1.47/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f56,plain,(
% 1.47/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.47/0.57    inference(rectify,[],[f55])).
% 1.47/0.57  fof(f55,plain,(
% 1.47/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.47/0.57    inference(nnf_transformation,[],[f1])).
% 1.47/0.57  fof(f1,axiom,(
% 1.47/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.47/0.57  fof(f164,plain,(
% 1.47/0.57    r2_hidden(sK6(k9_relat_1(sK3,sK2),k3_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))),k9_relat_1(sK3,sK2))),
% 1.47/0.57    inference(resolution,[],[f161,f93])).
% 1.47/0.57  fof(f93,plain,(
% 1.47/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f65])).
% 1.47/0.57  fof(f65,plain,(
% 1.47/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f63,f64])).
% 1.47/0.57  fof(f64,plain,(
% 1.47/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f63,plain,(
% 1.47/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.57    inference(rectify,[],[f62])).
% 1.47/0.57  fof(f62,plain,(
% 1.47/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.57    inference(nnf_transformation,[],[f47])).
% 1.47/0.57  fof(f47,plain,(
% 1.47/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f2])).
% 1.47/0.57  fof(f2,axiom,(
% 1.47/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.47/0.57  fof(f161,plain,(
% 1.47/0.57    ~r1_tarski(k9_relat_1(sK3,sK2),k3_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.47/0.57    inference(backward_demodulation,[],[f111,f119])).
% 1.47/0.57  fof(f119,plain,(
% 1.47/0.57    ( ! [X0] : (k7_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.47/0.57    inference(resolution,[],[f112,f107])).
% 1.47/0.57  fof(f107,plain,(
% 1.47/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f52])).
% 1.47/0.57  fof(f52,plain,(
% 1.47/0.57    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.57    inference(ennf_transformation,[],[f24])).
% 1.47/0.57  fof(f24,axiom,(
% 1.47/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.47/0.57  fof(f112,plain,(
% 1.47/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)))),
% 1.47/0.57    inference(definition_unfolding,[],[f70,f110])).
% 1.47/0.57  fof(f110,plain,(
% 1.47/0.57    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.47/0.57    inference(definition_unfolding,[],[f74,f109])).
% 1.47/0.57  fof(f109,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.47/0.57    inference(definition_unfolding,[],[f85,f108])).
% 1.47/0.57  fof(f108,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.47/0.57    inference(definition_unfolding,[],[f100,f106])).
% 1.47/0.57  fof(f106,plain,(
% 1.47/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f7])).
% 1.47/0.57  fof(f7,axiom,(
% 1.47/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.47/0.57  fof(f100,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f6])).
% 1.47/0.57  fof(f6,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.47/0.57  fof(f85,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f5])).
% 1.47/0.57  fof(f5,axiom,(
% 1.47/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.47/0.57  fof(f74,plain,(
% 1.47/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f4])).
% 1.47/0.57  fof(f4,axiom,(
% 1.47/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.47/0.57  fof(f70,plain,(
% 1.47/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.47/0.57    inference(cnf_transformation,[],[f54])).
% 1.47/0.57  fof(f54,plain,(
% 1.47/0.57    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 1.47/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f53])).
% 1.47/0.57  fof(f53,plain,(
% 1.47/0.57    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f32,plain,(
% 1.47/0.57    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.47/0.57    inference(flattening,[],[f31])).
% 1.47/0.57  fof(f31,plain,(
% 1.47/0.57    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.47/0.57    inference(ennf_transformation,[],[f28])).
% 1.47/0.57  % (28490)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (28490)Memory used [KB]: 10618
% 1.47/0.57  % (28490)Time elapsed: 0.151 s
% 1.47/0.57  % (28490)------------------------------
% 1.47/0.57  % (28490)------------------------------
% 1.47/0.58  fof(f28,plain,(
% 1.47/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.47/0.58    inference(pure_predicate_removal,[],[f27])).
% 1.47/0.58  fof(f27,negated_conjecture,(
% 1.47/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.47/0.58    inference(negated_conjecture,[],[f26])).
% 1.47/0.58  fof(f26,conjecture,(
% 1.47/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.47/0.58  fof(f111,plain,(
% 1.47/0.58    ~r1_tarski(k7_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k3_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.47/0.58    inference(definition_unfolding,[],[f72,f110,f110])).
% 1.47/0.58  fof(f72,plain,(
% 1.47/0.58    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.47/0.58    inference(cnf_transformation,[],[f54])).
% 1.47/0.58  fof(f574,plain,(
% 1.47/0.58    ~spl7_21 | spl7_26),
% 1.47/0.58    inference(avatar_contradiction_clause,[],[f573])).
% 1.47/0.58  fof(f573,plain,(
% 1.47/0.58    $false | (~spl7_21 | spl7_26)),
% 1.47/0.58    inference(subsumption_resolution,[],[f73,f540])).
% 1.47/0.58  fof(f540,plain,(
% 1.47/0.58    ~v1_xboole_0(k1_xboole_0) | (~spl7_21 | spl7_26)),
% 1.47/0.58    inference(backward_demodulation,[],[f481,f351])).
% 1.47/0.58  fof(f481,plain,(
% 1.47/0.58    ~v1_xboole_0(sK3) | spl7_26),
% 1.47/0.58    inference(resolution,[],[f469,f76])).
% 1.47/0.58  fof(f76,plain,(
% 1.47/0.58    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f34])).
% 1.47/0.58  fof(f34,plain,(
% 1.47/0.58    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.47/0.58    inference(ennf_transformation,[],[f14])).
% 1.47/0.58  fof(f14,axiom,(
% 1.47/0.58    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).
% 1.47/0.58  fof(f469,plain,(
% 1.47/0.58    ~v1_xboole_0(k2_relat_1(sK3)) | spl7_26),
% 1.47/0.58    inference(avatar_component_clause,[],[f468])).
% 1.47/0.58  fof(f468,plain,(
% 1.47/0.58    spl7_26 <=> v1_xboole_0(k2_relat_1(sK3))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 1.47/0.58  fof(f73,plain,(
% 1.47/0.58    v1_xboole_0(k1_xboole_0)),
% 1.47/0.58    inference(cnf_transformation,[],[f3])).
% 1.47/0.58  fof(f3,axiom,(
% 1.47/0.58    v1_xboole_0(k1_xboole_0)),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.47/0.58  fof(f501,plain,(
% 1.47/0.58    ~spl7_4 | ~spl7_19 | ~spl7_22),
% 1.47/0.58    inference(avatar_contradiction_clause,[],[f499])).
% 1.47/0.58  fof(f499,plain,(
% 1.47/0.58    $false | (~spl7_4 | ~spl7_19 | ~spl7_22)),
% 1.47/0.58    inference(resolution,[],[f493,f444])).
% 1.47/0.58  fof(f444,plain,(
% 1.47/0.58    ( ! [X1] : (r1_tarski(k9_relat_1(sK3,X1),k2_relat_1(sK3))) ) | (~spl7_4 | ~spl7_22)),
% 1.47/0.58    inference(forward_demodulation,[],[f379,f184])).
% 1.47/0.58  fof(f184,plain,(
% 1.47/0.58    k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) | ~spl7_4),
% 1.47/0.58    inference(superposition,[],[f158,f159])).
% 1.47/0.58  fof(f159,plain,(
% 1.47/0.58    sK3 = k7_relat_1(sK3,k1_relat_1(sK3)) | ~spl7_4),
% 1.47/0.58    inference(resolution,[],[f136,f77])).
% 1.47/0.58  fof(f77,plain,(
% 1.47/0.58    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 1.47/0.58    inference(cnf_transformation,[],[f35])).
% 1.47/0.58  fof(f35,plain,(
% 1.47/0.58    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.47/0.58    inference(ennf_transformation,[],[f21])).
% 1.47/0.58  fof(f21,axiom,(
% 1.47/0.58    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 1.47/0.58  fof(f136,plain,(
% 1.47/0.58    v1_relat_1(sK3) | ~spl7_4),
% 1.47/0.58    inference(avatar_component_clause,[],[f135])).
% 1.47/0.58  fof(f135,plain,(
% 1.47/0.58    spl7_4 <=> v1_relat_1(sK3)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.47/0.58  fof(f158,plain,(
% 1.47/0.58    ( ! [X0] : (k9_relat_1(sK3,X0) = k2_relat_1(k7_relat_1(sK3,X0))) ) | ~spl7_4),
% 1.47/0.58    inference(resolution,[],[f136,f87])).
% 1.47/0.58  fof(f87,plain,(
% 1.47/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 1.47/0.58    inference(cnf_transformation,[],[f41])).
% 1.47/0.58  fof(f41,plain,(
% 1.47/0.58    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.47/0.58    inference(ennf_transformation,[],[f18])).
% 1.47/0.58  fof(f18,axiom,(
% 1.47/0.58    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.47/0.58  fof(f379,plain,(
% 1.47/0.58    ( ! [X1] : (r1_tarski(k9_relat_1(sK3,X1),k9_relat_1(sK3,k1_relat_1(sK3)))) ) | ~spl7_22),
% 1.47/0.58    inference(avatar_component_clause,[],[f378])).
% 1.47/0.58  fof(f378,plain,(
% 1.47/0.58    spl7_22 <=> ! [X1] : r1_tarski(k9_relat_1(sK3,X1),k9_relat_1(sK3,k1_relat_1(sK3)))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 1.47/0.58  fof(f493,plain,(
% 1.47/0.58    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~spl7_19),
% 1.47/0.58    inference(backward_demodulation,[],[f161,f326])).
% 1.47/0.58  fof(f326,plain,(
% 1.47/0.58    k3_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl7_19),
% 1.47/0.58    inference(avatar_component_clause,[],[f325])).
% 1.47/0.58  fof(f325,plain,(
% 1.47/0.58    spl7_19 <=> k3_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.47/0.58  fof(f473,plain,(
% 1.47/0.58    ~spl7_26 | spl7_27 | ~spl7_17),
% 1.47/0.58    inference(avatar_split_clause,[],[f465,f293,f471,f468])).
% 1.47/0.58  fof(f293,plain,(
% 1.47/0.58    spl7_17 <=> ! [X1,X0] : (r2_hidden(X0,k2_relat_1(sK3)) | ~r2_hidden(X0,k9_relat_1(sK3,X1)))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.47/0.58  fof(f465,plain,(
% 1.47/0.58    ( ! [X0] : (v1_xboole_0(k9_relat_1(sK3,X0)) | ~v1_xboole_0(k2_relat_1(sK3))) ) | ~spl7_17),
% 1.47/0.58    inference(resolution,[],[f304,f81])).
% 1.47/0.58  fof(f304,plain,(
% 1.47/0.58    ( ! [X0] : (r2_hidden(sK4(k9_relat_1(sK3,X0)),k2_relat_1(sK3)) | v1_xboole_0(k9_relat_1(sK3,X0))) ) | ~spl7_17),
% 1.47/0.58    inference(resolution,[],[f294,f82])).
% 1.47/0.58  fof(f82,plain,(
% 1.47/0.58    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f58])).
% 1.47/0.58  fof(f294,plain,(
% 1.47/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(X0,k2_relat_1(sK3))) ) | ~spl7_17),
% 1.47/0.58    inference(avatar_component_clause,[],[f293])).
% 1.47/0.58  fof(f464,plain,(
% 1.47/0.58    ~spl7_4 | ~spl7_18 | spl7_19 | ~spl7_11),
% 1.47/0.58    inference(avatar_split_clause,[],[f463,f199,f325,f322,f135])).
% 1.47/0.58  fof(f322,plain,(
% 1.47/0.58    spl7_18 <=> v1_funct_1(sK3)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 1.47/0.59  fof(f199,plain,(
% 1.47/0.59    spl7_11 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 1.47/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.47/0.59  fof(f463,plain,(
% 1.47/0.59    k3_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl7_11),
% 1.47/0.59    inference(equality_resolution,[],[f434])).
% 1.47/0.59  fof(f434,plain,(
% 1.47/0.59    ( ! [X1] : (k1_relat_1(X1) != k1_relat_1(sK3) | k2_relat_1(X1) = k3_enumset1(k1_funct_1(X1,sK0),k1_funct_1(X1,sK0),k1_funct_1(X1,sK0),k1_funct_1(X1,sK0),k1_funct_1(X1,sK0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl7_11),
% 1.47/0.59    inference(superposition,[],[f113,f200])).
% 1.47/0.59  fof(f200,plain,(
% 1.47/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl7_11),
% 1.47/0.59    inference(avatar_component_clause,[],[f199])).
% 1.47/0.59  fof(f113,plain,(
% 1.47/0.59    ( ! [X0,X1] : (k1_relat_1(X1) != k3_enumset1(X0,X0,X0,X0,X0) | k2_relat_1(X1) = k3_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.47/0.59    inference(definition_unfolding,[],[f90,f110,f110])).
% 1.47/0.59  fof(f90,plain,(
% 1.47/0.59    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f44])).
% 1.47/0.59  fof(f44,plain,(
% 1.47/0.59    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.47/0.59    inference(flattening,[],[f43])).
% 1.47/0.59  fof(f43,plain,(
% 1.47/0.59    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.47/0.59    inference(ennf_transformation,[],[f22])).
% 1.47/0.59  fof(f22,axiom,(
% 1.47/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.47/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.47/0.59  fof(f388,plain,(
% 1.47/0.59    spl7_11 | spl7_12 | ~spl7_7),
% 1.47/0.59    inference(avatar_split_clause,[],[f385,f152,f202,f199])).
% 1.47/0.59  fof(f202,plain,(
% 1.47/0.59    spl7_12 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 1.47/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.47/0.59  fof(f152,plain,(
% 1.47/0.59    spl7_7 <=> r1_tarski(k1_relat_1(sK3),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.47/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.47/0.59  fof(f385,plain,(
% 1.47/0.59    k1_xboole_0 = k1_relat_1(sK3) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl7_7),
% 1.47/0.59    inference(resolution,[],[f153,f116])).
% 1.47/0.59  fof(f116,plain,(
% 1.47/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 1.47/0.59    inference(definition_unfolding,[],[f95,f110,f110])).
% 1.47/0.59  fof(f95,plain,(
% 1.47/0.59    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.47/0.59    inference(cnf_transformation,[],[f67])).
% 1.47/0.59  fof(f67,plain,(
% 1.47/0.59    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.47/0.59    inference(flattening,[],[f66])).
% 1.47/0.59  fof(f66,plain,(
% 1.47/0.59    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.47/0.59    inference(nnf_transformation,[],[f8])).
% 1.47/0.59  fof(f8,axiom,(
% 1.47/0.59    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.47/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.47/0.59  fof(f153,plain,(
% 1.47/0.59    r1_tarski(k1_relat_1(sK3),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl7_7),
% 1.47/0.59    inference(avatar_component_clause,[],[f152])).
% 1.47/0.59  fof(f380,plain,(
% 1.47/0.59    ~spl7_4 | spl7_22 | ~spl7_4),
% 1.47/0.59    inference(avatar_split_clause,[],[f369,f135,f378,f135])).
% 1.47/0.59  fof(f369,plain,(
% 1.47/0.59    ( ! [X1] : (r1_tarski(k9_relat_1(sK3,X1),k9_relat_1(sK3,k1_relat_1(sK3))) | ~v1_relat_1(sK3)) ) | ~spl7_4),
% 1.47/0.59    inference(superposition,[],[f185,f159])).
% 1.47/0.59  fof(f185,plain,(
% 1.47/0.59    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(sK3,X0),X1),k9_relat_1(sK3,X0)) | ~v1_relat_1(k7_relat_1(sK3,X0))) ) | ~spl7_4),
% 1.47/0.59    inference(superposition,[],[f86,f158])).
% 1.47/0.59  fof(f86,plain,(
% 1.47/0.59    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f40])).
% 1.47/0.59  fof(f40,plain,(
% 1.47/0.59    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.47/0.59    inference(ennf_transformation,[],[f17])).
% 1.47/0.59  fof(f17,axiom,(
% 1.47/0.59    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.47/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.47/0.59  fof(f357,plain,(
% 1.47/0.59    ~spl7_4 | spl7_7),
% 1.47/0.59    inference(avatar_split_clause,[],[f355,f152,f135])).
% 1.47/0.59  fof(f355,plain,(
% 1.47/0.59    r1_tarski(k1_relat_1(sK3),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK3)),
% 1.47/0.59    inference(resolution,[],[f120,f88])).
% 1.47/0.59  fof(f88,plain,(
% 1.47/0.59    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f61])).
% 1.47/0.59  fof(f61,plain,(
% 1.47/0.59    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.47/0.59    inference(nnf_transformation,[],[f42])).
% 1.47/0.59  fof(f42,plain,(
% 1.47/0.59    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.47/0.59    inference(ennf_transformation,[],[f13])).
% 1.47/0.59  fof(f13,axiom,(
% 1.47/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.47/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.47/0.59  fof(f120,plain,(
% 1.47/0.59    v4_relat_1(sK3,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.47/0.59    inference(resolution,[],[f112,f101])).
% 1.47/0.59  fof(f101,plain,(
% 1.47/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f48])).
% 1.47/0.59  fof(f48,plain,(
% 1.47/0.59    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.59    inference(ennf_transformation,[],[f30])).
% 1.47/0.59  fof(f30,plain,(
% 1.47/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.47/0.59    inference(pure_predicate_removal,[],[f23])).
% 1.47/0.59  fof(f23,axiom,(
% 1.47/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.47/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.47/0.59  fof(f352,plain,(
% 1.47/0.59    ~spl7_4 | spl7_21 | ~spl7_12),
% 1.47/0.59    inference(avatar_split_clause,[],[f344,f202,f350,f135])).
% 1.47/0.59  fof(f344,plain,(
% 1.47/0.59    k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl7_12),
% 1.47/0.59    inference(trivial_inequality_removal,[],[f343])).
% 1.47/0.59  fof(f343,plain,(
% 1.47/0.59    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl7_12),
% 1.47/0.59    inference(superposition,[],[f78,f203])).
% 1.47/0.59  fof(f203,plain,(
% 1.47/0.59    k1_xboole_0 = k1_relat_1(sK3) | ~spl7_12),
% 1.47/0.59    inference(avatar_component_clause,[],[f202])).
% 1.47/0.59  fof(f78,plain,(
% 1.47/0.59    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f37])).
% 1.47/0.59  fof(f37,plain,(
% 1.47/0.59    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.47/0.59    inference(flattening,[],[f36])).
% 1.47/0.59  fof(f36,plain,(
% 1.47/0.59    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.47/0.59    inference(ennf_transformation,[],[f20])).
% 1.47/0.59  fof(f20,axiom,(
% 1.47/0.59    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.47/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.47/0.59  fof(f329,plain,(
% 1.47/0.59    spl7_18),
% 1.47/0.59    inference(avatar_contradiction_clause,[],[f328])).
% 1.47/0.59  fof(f328,plain,(
% 1.47/0.59    $false | spl7_18),
% 1.47/0.59    inference(subsumption_resolution,[],[f69,f323])).
% 1.47/0.59  fof(f323,plain,(
% 1.47/0.59    ~v1_funct_1(sK3) | spl7_18),
% 1.47/0.59    inference(avatar_component_clause,[],[f322])).
% 1.47/0.59  fof(f69,plain,(
% 1.47/0.59    v1_funct_1(sK3)),
% 1.47/0.59    inference(cnf_transformation,[],[f54])).
% 1.47/0.59  fof(f295,plain,(
% 1.47/0.59    ~spl7_4 | spl7_17 | ~spl7_4),
% 1.47/0.59    inference(avatar_split_clause,[],[f291,f135,f293,f135])).
% 1.47/0.59  fof(f291,plain,(
% 1.47/0.59    ( ! [X0,X1] : (r2_hidden(X0,k2_relat_1(sK3)) | ~r2_hidden(X0,k9_relat_1(sK3,X1)) | ~v1_relat_1(sK3)) ) | ~spl7_4),
% 1.47/0.59    inference(forward_demodulation,[],[f289,f184])).
% 1.47/0.59  fof(f289,plain,(
% 1.47/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | ~v1_relat_1(sK3) | r2_hidden(X0,k9_relat_1(sK3,k1_relat_1(sK3)))) ) | ~spl7_4),
% 1.47/0.59    inference(superposition,[],[f270,f159])).
% 1.47/0.59  fof(f270,plain,(
% 1.47/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X1,k9_relat_1(k7_relat_1(sK3,X0),X2)) | ~v1_relat_1(k7_relat_1(sK3,X0)) | r2_hidden(X1,k9_relat_1(sK3,X0))) ) | ~spl7_4),
% 1.47/0.59    inference(resolution,[],[f185,f92])).
% 1.47/0.59  fof(f92,plain,(
% 1.47/0.59    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f65])).
% 1.47/0.59  fof(f157,plain,(
% 1.47/0.59    spl7_3),
% 1.47/0.59    inference(avatar_contradiction_clause,[],[f155])).
% 1.47/0.59  fof(f155,plain,(
% 1.47/0.59    $false | spl7_3),
% 1.47/0.59    inference(resolution,[],[f133,f84])).
% 1.47/0.59  fof(f84,plain,(
% 1.47/0.59    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.47/0.59    inference(cnf_transformation,[],[f16])).
% 1.47/0.59  fof(f16,axiom,(
% 1.47/0.59    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.47/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.47/0.59  fof(f133,plain,(
% 1.47/0.59    ~v1_relat_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) | spl7_3),
% 1.47/0.59    inference(avatar_component_clause,[],[f132])).
% 1.47/0.59  fof(f132,plain,(
% 1.47/0.59    spl7_3 <=> v1_relat_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.47/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.47/0.59  fof(f137,plain,(
% 1.47/0.59    ~spl7_3 | spl7_4),
% 1.47/0.59    inference(avatar_split_clause,[],[f123,f135,f132])).
% 1.47/0.59  fof(f123,plain,(
% 1.47/0.59    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.47/0.59    inference(resolution,[],[f112,f80])).
% 1.47/0.59  fof(f80,plain,(
% 1.47/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f38])).
% 1.47/0.59  fof(f38,plain,(
% 1.47/0.59    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.47/0.59    inference(ennf_transformation,[],[f12])).
% 1.47/0.59  fof(f12,axiom,(
% 1.47/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.47/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.47/0.59  % SZS output end Proof for theBenchmark
% 1.47/0.59  % (28472)------------------------------
% 1.47/0.59  % (28472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.59  % (28472)Termination reason: Refutation
% 1.47/0.59  
% 1.47/0.59  % (28472)Memory used [KB]: 11001
% 1.47/0.59  % (28472)Time elapsed: 0.172 s
% 1.47/0.59  % (28472)------------------------------
% 1.47/0.59  % (28472)------------------------------
% 1.47/0.59  % (28466)Success in time 0.227 s
%------------------------------------------------------------------------------
