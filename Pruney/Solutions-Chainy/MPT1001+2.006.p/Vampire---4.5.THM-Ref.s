%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 756 expanded)
%              Number of leaves         :   22 ( 189 expanded)
%              Depth                    :   24
%              Number of atoms          :  356 (3693 expanded)
%              Number of equality atoms :   93 (1497 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f86,f116,f184])).

fof(f184,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f178,f177])).

fof(f177,plain,
    ( ! [X2] : sP6(X2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f172,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | sP6(X1) ) ),
    inference(cnf_transformation,[],[f67_D])).

% (27012)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f67_D,plain,(
    ! [X1] :
      ( ! [X0] : ~ r2_hidden(X0,X1)
    <=> ~ sP6(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f172,plain,
    ( ! [X0] : r2_hidden(sK3,X0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f171,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f171,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | r2_hidden(sK3,X0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(superposition,[],[f55,f166])).

fof(f166,plain,
    ( k1_xboole_0 = k1_tarski(sK3)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f165,f164])).

fof(f164,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f162,f91])).

fof(f91,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f89,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(f89,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f43,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ( k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))
        & r2_hidden(sK3,sK1) ) )
    & ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | ! [X4] :
          ( k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4))
          | ~ r2_hidden(X4,sK1) ) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f32,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ? [X3] :
              ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
              & r2_hidden(X3,X1) ) )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ! [X4] :
              ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X4))
              | ~ r2_hidden(X4,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
        | ? [X3] :
            ( k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(X3))
            & r2_hidden(X3,sK1) ) )
      & ( sK1 = k2_relset_1(sK0,sK1,sK2)
        | ! [X4] :
            ( k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4))
            | ~ r2_hidden(X4,sK1) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X3] :
        ( k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(X3))
        & r2_hidden(X3,sK1) )
   => ( k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))
      & r2_hidden(sK3,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X4] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X4))
            | ~ r2_hidden(X4,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3))
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3))
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3))
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3))
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_2)).

fof(f162,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0))
    | ~ spl7_2 ),
    inference(resolution,[],[f147,f47])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f146,f89])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
        | ~ v1_relat_1(sK2) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f144,f42])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_2 ),
    inference(superposition,[],[f51,f139])).

fof(f139,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f88,f75])).

fof(f75,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl7_2
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f88,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f43,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f165,plain,
    ( k1_tarski(sK3) = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f163,f150])).

fof(f150,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK3))
    | ~ spl7_1 ),
    inference(superposition,[],[f72,f87])).

fof(f87,plain,(
    ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(resolution,[],[f43,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f72,plain,
    ( k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl7_1
  <=> k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f163,plain,
    ( k1_tarski(sK3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_tarski(sK3)))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f147,f126])).

fof(f126,plain,
    ( r1_tarski(k1_tarski(sK3),sK1)
    | ~ spl7_3 ),
    inference(resolution,[],[f81,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f81,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl7_3
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f178,plain,
    ( ! [X0] : ~ sP6(X0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f175,f172])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | ~ sP6(X0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f172,f68])).

fof(f68,plain,(
    ! [X3,X1] :
      ( ~ r2_hidden(X3,sK5(X1))
      | ~ r2_hidden(X3,X1)
      | ~ sP6(X1) ) ),
    inference(general_splitting,[],[f60,f67_D])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK5(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f40])).

fof(f40,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f116,plain,
    ( spl7_2
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f114,f89])).

fof(f114,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f113,f107])).

fof(f107,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f106,f102])).

fof(f102,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl7_2 ),
    inference(superposition,[],[f76,f88])).

fof(f76,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f106,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(resolution,[],[f105,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f105,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f104,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

% (27019)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f104,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f103,f43])).

fof(f103,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f63,f88])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

% (27030)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (27033)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (27028)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f113,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl7_2
    | ~ spl7_4 ),
    inference(resolution,[],[f112,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1)))
        & r2_hidden(sK4(X0,X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
          & r2_hidden(X2,X0) )
     => ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1)))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ? [X2] :
          ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ? [X2] :
          ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_1)).

fof(f112,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK1)
    | spl7_2
    | ~ spl7_4 ),
    inference(trivial_inequality_removal,[],[f111])).

fof(f111,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK4(sK1,sK2),sK1)
    | spl7_2
    | ~ spl7_4 ),
    inference(superposition,[],[f110,f109])).

fof(f109,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(sK1,sK2)))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f108,f89])).

fof(f108,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(sK1,sK2)))
    | ~ v1_relat_1(sK2)
    | spl7_2 ),
    inference(resolution,[],[f107,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f110,plain,
    ( ! [X4] :
        ( k1_xboole_0 != k10_relat_1(sK2,k1_tarski(X4))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f85,f87])).

fof(f85,plain,
    ( ! [X4] :
        ( k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_4
  <=> ! [X4] :
        ( k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4))
        | ~ r2_hidden(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f86,plain,
    ( spl7_4
    | spl7_2 ),
    inference(avatar_split_clause,[],[f44,f74,f84])).

fof(f44,plain,(
    ! [X4] :
      ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4))
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,
    ( spl7_3
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f45,f74,f79])).

fof(f45,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f46,f74,f70])).

fof(f46,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:55:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (27027)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.50  % (27008)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (27022)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (27009)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (27010)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (27025)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (27026)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (27009)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f77,f82,f86,f116,f184])).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    ~spl7_1 | ~spl7_2 | ~spl7_3),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f183])).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    $false | (~spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f178,f177])).
% 0.22/0.52  fof(f177,plain,(
% 0.22/0.52    ( ! [X2] : (sP6(X2)) ) | (~spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.22/0.52    inference(resolution,[],[f172,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | sP6(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f67_D])).
% 0.22/0.52  % (27012)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  fof(f67_D,plain,(
% 0.22/0.52    ( ! [X1] : (( ! [X0] : ~r2_hidden(X0,X1) ) <=> ~sP6(X1)) )),
% 0.22/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK3,X0)) ) | (~spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f171,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r2_hidden(sK3,X0)) ) | (~spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.22/0.52    inference(superposition,[],[f55,f166])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    k1_xboole_0 = k1_tarski(sK3) | (~spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.22/0.52    inference(forward_demodulation,[],[f165,f164])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | ~spl7_2),
% 0.22/0.52    inference(forward_demodulation,[],[f162,f91])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)),
% 0.22/0.52    inference(resolution,[],[f89,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    v1_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f43,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    (sK1 != k2_relset_1(sK0,sK1,sK2) | (k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) & r2_hidden(sK3,sK1))) & (sK1 = k2_relset_1(sK0,sK1,sK2) | ! [X4] : (k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4)) | ~r2_hidden(X4,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f32,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X4] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X4)) | ~r2_hidden(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((sK1 != k2_relset_1(sK0,sK1,sK2) | ? [X3] : (k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(X3)) & r2_hidden(X3,sK1))) & (sK1 = k2_relset_1(sK0,sK1,sK2) | ! [X4] : (k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4)) | ~r2_hidden(X4,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ? [X3] : (k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(X3)) & r2_hidden(X3,sK1)) => (k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) & r2_hidden(sK3,sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X4] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X4)) | ~r2_hidden(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.22/0.52    inference(rectify,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3)) | ~r2_hidden(X3,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3)) | ~r2_hidden(X3,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.22/0.52    inference(nnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((! [X3] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3)) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((! [X3] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3)) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f14])).
% 0.22/0.52  fof(f14,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.52    inference(negated_conjecture,[],[f13])).
% 0.22/0.52  fof(f13,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_2)).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) | ~spl7_2),
% 0.22/0.52    inference(resolution,[],[f147,f47])).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) ) | ~spl7_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f146,f89])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 | ~v1_relat_1(sK2)) ) | ~spl7_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f144,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    v1_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl7_2),
% 0.22/0.52    inference(superposition,[],[f51,f139])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    sK1 = k2_relat_1(sK2) | ~spl7_2),
% 0.22/0.52    inference(backward_demodulation,[],[f88,f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl7_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    spl7_2 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f43,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    k1_tarski(sK3) = k9_relat_1(sK2,k1_xboole_0) | (~spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.22/0.52    inference(forward_demodulation,[],[f163,f150])).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK3)) | ~spl7_1),
% 0.22/0.52    inference(superposition,[],[f72,f87])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ( ! [X0] : (k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)) )),
% 0.22/0.52    inference(resolution,[],[f43,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) | ~spl7_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    spl7_1 <=> k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    k1_tarski(sK3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_tarski(sK3))) | (~spl7_2 | ~spl7_3)),
% 0.22/0.52    inference(resolution,[],[f147,f126])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    r1_tarski(k1_tarski(sK3),sK1) | ~spl7_3),
% 0.22/0.52    inference(resolution,[],[f81,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    r2_hidden(sK3,sK1) | ~spl7_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f79])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    spl7_3 <=> r2_hidden(sK3,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    ( ! [X0] : (~sP6(X0)) ) | (~spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f175,f172])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(sK3,X0) | ~sP6(X0)) ) | (~spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.22/0.52    inference(resolution,[],[f172,f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X3,X1] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1) | ~sP6(X1)) )),
% 0.22/0.52    inference(general_splitting,[],[f60,f67_D])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X1),X1)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    spl7_2 | ~spl7_4),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f115])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    $false | (spl7_2 | ~spl7_4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f114,f89])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | (spl7_2 | ~spl7_4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f113,f107])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    ~r1_tarski(sK1,k2_relat_1(sK2)) | spl7_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f106,f102])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    sK1 != k2_relat_1(sK2) | spl7_2),
% 0.22/0.52    inference(superposition,[],[f76,f88])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    sK1 != k2_relset_1(sK0,sK1,sK2) | spl7_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f74])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    sK1 = k2_relat_1(sK2) | ~r1_tarski(sK1,k2_relat_1(sK2))),
% 0.22/0.52    inference(resolution,[],[f105,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.52    inference(resolution,[],[f104,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  % (27019)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f103,f43])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(superposition,[],[f63,f88])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.22/0.52  % (27030)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (27033)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (27028)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    r1_tarski(sK1,k2_relat_1(sK2)) | ~v1_relat_1(sK2) | (spl7_2 | ~spl7_4)),
% 0.22/0.52    inference(resolution,[],[f112,f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | (k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1))) & r2_hidden(sK4(X0,X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : (k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) => (k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1))) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | ? [X2] : (k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_tarski(X0,k2_relat_1(X1)) | ? [X2] : (k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0))) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : ~(k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_1)).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    ~r2_hidden(sK4(sK1,sK2),sK1) | (spl7_2 | ~spl7_4)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f111])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK4(sK1,sK2),sK1) | (spl7_2 | ~spl7_4)),
% 0.22/0.52    inference(superposition,[],[f110,f109])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(sK1,sK2))) | spl7_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f108,f89])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(sK1,sK2))) | ~v1_relat_1(sK2) | spl7_2),
% 0.22/0.52    inference(resolution,[],[f107,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1))) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    ( ! [X4] : (k1_xboole_0 != k10_relat_1(sK2,k1_tarski(X4)) | ~r2_hidden(X4,sK1)) ) | ~spl7_4),
% 0.22/0.52    inference(backward_demodulation,[],[f85,f87])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    ( ! [X4] : (k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4)) | ~r2_hidden(X4,sK1)) ) | ~spl7_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f84])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    spl7_4 <=> ! [X4] : (k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4)) | ~r2_hidden(X4,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    spl7_4 | spl7_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f44,f74,f84])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X4] : (sK1 = k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4)) | ~r2_hidden(X4,sK1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    spl7_3 | ~spl7_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f45,f74,f79])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    sK1 != k2_relset_1(sK0,sK1,sK2) | r2_hidden(sK3,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    spl7_1 | ~spl7_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f46,f74,f70])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (27009)------------------------------
% 0.22/0.52  % (27009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (27009)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (27009)Memory used [KB]: 10618
% 0.22/0.52  % (27009)Time elapsed: 0.096 s
% 0.22/0.52  % (27009)------------------------------
% 0.22/0.52  % (27009)------------------------------
% 0.22/0.52  % (27011)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (27014)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (27007)Success in time 0.155 s
%------------------------------------------------------------------------------
