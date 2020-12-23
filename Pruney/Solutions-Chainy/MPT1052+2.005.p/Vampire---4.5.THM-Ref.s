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
% DateTime   : Thu Dec  3 13:07:03 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 511 expanded)
%              Number of leaves         :   24 ( 147 expanded)
%              Depth                    :   16
%              Number of atoms          :  354 (1560 expanded)
%              Number of equality atoms :   80 ( 297 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (32569)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f221,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f124,f126,f153,f156,f213,f216,f220])).

fof(f220,plain,
    ( spl6_1
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | spl6_1
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(trivial_inequality_removal,[],[f218])).

fof(f218,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl6_1
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(superposition,[],[f187,f212])).

fof(f212,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl6_7
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f187,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | spl6_1
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f85,f183])).

fof(f183,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_4 ),
    inference(superposition,[],[f180,f95])).

fof(f95,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f94,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f94,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f93,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f93,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f57,f91])).

fof(f91,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f48,f47])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f180,plain,
    ( ! [X2] : k2_xboole_0(sK1,X2) = X2
    | ~ spl6_4 ),
    inference(resolution,[],[f176,f54])).

fof(f176,plain,
    ( ! [X0] : r1_tarski(sK1,X0)
    | ~ spl6_4 ),
    inference(resolution,[],[f173,f57])).

fof(f173,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl6_4 ),
    inference(resolution,[],[f157,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)))
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f111,f47])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,k5_partfun1(X2,X0,k3_partfun1(k1_xboole_0,X2,X0)))
      | ~ r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f110,f48])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) ) ),
    inference(resolution,[],[f73,f48])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f55,f51])).

fof(f51,plain,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_funct_2)).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

fof(f157,plain,
    ( r2_hidden(sK3,k5_partfun1(sK1,k1_xboole_0,k3_partfun1(k1_xboole_0,sK1,k1_xboole_0)))
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f72,f148])).

fof(f148,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f72,plain,(
    r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f45,plain,(
    r2_hidden(sK3,k1_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r1_tarski(k2_relat_1(sK3),sK2)
      | sK1 != k1_relat_1(sK3) )
    & r2_hidden(sK3,k1_funct_2(sK1,sK2))
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k2_relat_1(X2),X1)
          | k1_relat_1(X2) != X0 )
        & r2_hidden(X2,k1_funct_2(X0,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k2_relat_1(sK3),sK2)
        | sK1 != k1_relat_1(sK3) )
      & r2_hidden(sK3,k1_funct_2(sK1,sK2))
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

fof(f85,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl6_1
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f216,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_6 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6 ),
    inference(resolution,[],[f208,f193])).

fof(f193,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f167,f183])).

fof(f167,plain,
    ( v1_funct_2(sK3,sK1,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f151,f148])).

fof(f151,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl6_5
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f208,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl6_6
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f213,plain,
    ( ~ spl6_6
    | spl6_7
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f204,f146,f210,f206])).

fof(f204,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f202,f191])).

fof(f191,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f160,f183])).

fof(f160,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK1,k1_xboole_0,sK3)
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f115,f148])).

fof(f115,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f112,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f112,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f74,f72])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f61,f51])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f202,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl6_4 ),
    inference(resolution,[],[f192,f78])).

fof(f78,plain,(
    ! [X2,X1] :
      ( ~ sP0(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X1,k1_xboole_0,X2)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 != X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f192,plain,
    ( sP0(k1_xboole_0,sK3,k1_xboole_0)
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f161,f183])).

fof(f161,plain,
    ( sP0(sK1,sK3,k1_xboole_0)
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f116,f148])).

fof(f116,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f112,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(definition_folding,[],[f26,f27])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f156,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl6_5 ),
    inference(resolution,[],[f154,f72])).

fof(f154,plain,
    ( ~ r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2)))
    | spl6_5 ),
    inference(resolution,[],[f152,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f60,f51])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f152,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f150])).

fof(f153,plain,
    ( spl6_4
    | ~ spl6_5
    | spl6_1 ),
    inference(avatar_split_clause,[],[f144,f83,f150,f146])).

fof(f144,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f143,f115])).

fof(f143,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f65,f116])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f126,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl6_3 ),
    inference(resolution,[],[f123,f43])).

fof(f43,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f123,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl6_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f124,plain,
    ( ~ spl6_3
    | spl6_2 ),
    inference(avatar_split_clause,[],[f119,f87,f121])).

fof(f87,plain,
    ( spl6_2
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f119,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f117,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f117,plain,(
    v5_relat_1(sK3,sK2) ),
    inference(resolution,[],[f112,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f90,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f46,f87,f83])).

fof(f46,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | sK1 != k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:31:08 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (32555)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (32556)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (32548)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.54  % (32571)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.55  % (32545)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.41/0.55  % (32544)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.55  % (32564)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.41/0.56  % (32549)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.56  % (32546)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.54/0.57  % (32565)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.54/0.57  % (32554)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.54/0.57  % (32551)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.54/0.57  % (32554)Refutation found. Thanks to Tanya!
% 1.54/0.57  % SZS status Theorem for theBenchmark
% 1.54/0.57  % SZS output start Proof for theBenchmark
% 1.54/0.57  % (32569)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.54/0.57  fof(f221,plain,(
% 1.54/0.57    $false),
% 1.54/0.57    inference(avatar_sat_refutation,[],[f90,f124,f126,f153,f156,f213,f216,f220])).
% 1.54/0.57  fof(f220,plain,(
% 1.54/0.57    spl6_1 | ~spl6_4 | ~spl6_7),
% 1.54/0.57    inference(avatar_contradiction_clause,[],[f219])).
% 1.54/0.57  fof(f219,plain,(
% 1.54/0.57    $false | (spl6_1 | ~spl6_4 | ~spl6_7)),
% 1.54/0.57    inference(trivial_inequality_removal,[],[f218])).
% 1.54/0.57  fof(f218,plain,(
% 1.54/0.57    k1_xboole_0 != k1_xboole_0 | (spl6_1 | ~spl6_4 | ~spl6_7)),
% 1.54/0.57    inference(superposition,[],[f187,f212])).
% 1.54/0.57  fof(f212,plain,(
% 1.54/0.57    k1_xboole_0 = k1_relat_1(sK3) | ~spl6_7),
% 1.54/0.57    inference(avatar_component_clause,[],[f210])).
% 1.54/0.57  fof(f210,plain,(
% 1.54/0.57    spl6_7 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.54/0.57  fof(f187,plain,(
% 1.54/0.57    k1_xboole_0 != k1_relat_1(sK3) | (spl6_1 | ~spl6_4)),
% 1.54/0.57    inference(backward_demodulation,[],[f85,f183])).
% 1.54/0.57  fof(f183,plain,(
% 1.54/0.57    k1_xboole_0 = sK1 | ~spl6_4),
% 1.54/0.57    inference(superposition,[],[f180,f95])).
% 1.54/0.57  fof(f95,plain,(
% 1.54/0.57    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 1.54/0.57    inference(superposition,[],[f94,f50])).
% 1.54/0.57  fof(f50,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f1])).
% 1.54/0.57  fof(f1,axiom,(
% 1.54/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.54/0.57  fof(f94,plain,(
% 1.54/0.57    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.54/0.57    inference(resolution,[],[f93,f54])).
% 1.54/0.57  fof(f54,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.54/0.57    inference(cnf_transformation,[],[f18])).
% 1.54/0.57  fof(f18,plain,(
% 1.54/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.54/0.57    inference(ennf_transformation,[],[f5])).
% 1.54/0.57  fof(f5,axiom,(
% 1.54/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.54/0.57  fof(f93,plain,(
% 1.54/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.54/0.57    inference(resolution,[],[f57,f91])).
% 1.54/0.57  fof(f91,plain,(
% 1.54/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.54/0.57    inference(resolution,[],[f48,f47])).
% 1.54/0.57  fof(f47,plain,(
% 1.54/0.57    v1_xboole_0(k1_xboole_0)),
% 1.54/0.57    inference(cnf_transformation,[],[f4])).
% 1.54/0.57  fof(f4,axiom,(
% 1.54/0.57    v1_xboole_0(k1_xboole_0)),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.54/0.57  fof(f48,plain,(
% 1.54/0.57    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f34])).
% 1.54/0.57  fof(f34,plain,(
% 1.54/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.54/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 1.54/0.57  fof(f33,plain,(
% 1.54/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.54/0.57    introduced(choice_axiom,[])).
% 1.54/0.57  fof(f32,plain,(
% 1.54/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.54/0.57    inference(rectify,[],[f31])).
% 1.54/0.57  fof(f31,plain,(
% 1.54/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.54/0.57    inference(nnf_transformation,[],[f2])).
% 1.54/0.57  fof(f2,axiom,(
% 1.54/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.54/0.57  fof(f57,plain,(
% 1.54/0.57    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f39])).
% 1.54/0.57  fof(f39,plain,(
% 1.54/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.54/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 1.54/0.57  fof(f38,plain,(
% 1.54/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.54/0.57    introduced(choice_axiom,[])).
% 1.54/0.57  fof(f37,plain,(
% 1.54/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.54/0.57    inference(rectify,[],[f36])).
% 1.54/0.57  fof(f36,plain,(
% 1.54/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.54/0.57    inference(nnf_transformation,[],[f21])).
% 1.54/0.57  fof(f21,plain,(
% 1.54/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.54/0.57    inference(ennf_transformation,[],[f3])).
% 1.54/0.57  fof(f3,axiom,(
% 1.54/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.54/0.57  fof(f180,plain,(
% 1.54/0.57    ( ! [X2] : (k2_xboole_0(sK1,X2) = X2) ) | ~spl6_4),
% 1.54/0.57    inference(resolution,[],[f176,f54])).
% 1.54/0.57  fof(f176,plain,(
% 1.54/0.57    ( ! [X0] : (r1_tarski(sK1,X0)) ) | ~spl6_4),
% 1.54/0.57    inference(resolution,[],[f173,f57])).
% 1.54/0.57  fof(f173,plain,(
% 1.54/0.57    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl6_4),
% 1.54/0.57    inference(resolution,[],[f157,f136])).
% 1.54/0.57  fof(f136,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0))) | ~r2_hidden(X2,X1)) )),
% 1.54/0.57    inference(resolution,[],[f111,f47])).
% 1.54/0.57  fof(f111,plain,(
% 1.54/0.57    ( ! [X2,X0,X3,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,k5_partfun1(X2,X0,k3_partfun1(k1_xboole_0,X2,X0))) | ~r2_hidden(X3,X2)) )),
% 1.54/0.57    inference(resolution,[],[f110,f48])).
% 1.54/0.57  fof(f110,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~v1_xboole_0(X0) | ~r2_hidden(X2,k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0)))) )),
% 1.54/0.57    inference(resolution,[],[f73,f48])).
% 1.54/0.57  fof(f73,plain,(
% 1.54/0.57    ( ! [X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.54/0.57    inference(definition_unfolding,[],[f55,f51])).
% 1.54/0.57  fof(f51,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f12])).
% 1.54/0.57  fof(f12,axiom,(
% 1.54/0.57    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_funct_2)).
% 1.54/0.57  fof(f55,plain,(
% 1.54/0.57    ( ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f20])).
% 1.54/0.57  fof(f20,plain,(
% 1.54/0.57    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.54/0.57    inference(flattening,[],[f19])).
% 1.54/0.57  fof(f19,plain,(
% 1.54/0.57    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.54/0.57    inference(ennf_transformation,[],[f10])).
% 1.54/0.57  fof(f10,axiom,(
% 1.54/0.57    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).
% 1.54/0.57  fof(f157,plain,(
% 1.54/0.57    r2_hidden(sK3,k5_partfun1(sK1,k1_xboole_0,k3_partfun1(k1_xboole_0,sK1,k1_xboole_0))) | ~spl6_4),
% 1.54/0.57    inference(backward_demodulation,[],[f72,f148])).
% 1.54/0.57  fof(f148,plain,(
% 1.54/0.57    k1_xboole_0 = sK2 | ~spl6_4),
% 1.54/0.57    inference(avatar_component_clause,[],[f146])).
% 1.54/0.57  fof(f146,plain,(
% 1.54/0.57    spl6_4 <=> k1_xboole_0 = sK2),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.54/0.57  fof(f72,plain,(
% 1.54/0.57    r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2)))),
% 1.54/0.57    inference(definition_unfolding,[],[f45,f51])).
% 1.54/0.57  fof(f45,plain,(
% 1.54/0.57    r2_hidden(sK3,k1_funct_2(sK1,sK2))),
% 1.54/0.57    inference(cnf_transformation,[],[f30])).
% 1.54/0.57  fof(f30,plain,(
% 1.54/0.57    (~r1_tarski(k2_relat_1(sK3),sK2) | sK1 != k1_relat_1(sK3)) & r2_hidden(sK3,k1_funct_2(sK1,sK2)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 1.54/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f29])).
% 1.54/0.57  fof(f29,plain,(
% 1.54/0.57    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => ((~r1_tarski(k2_relat_1(sK3),sK2) | sK1 != k1_relat_1(sK3)) & r2_hidden(sK3,k1_funct_2(sK1,sK2)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 1.54/0.57    introduced(choice_axiom,[])).
% 1.54/0.57  fof(f16,plain,(
% 1.54/0.57    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.54/0.57    inference(flattening,[],[f15])).
% 1.54/0.57  fof(f15,plain,(
% 1.54/0.57    ? [X0,X1,X2] : (((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.54/0.57    inference(ennf_transformation,[],[f14])).
% 1.54/0.57  fof(f14,negated_conjecture,(
% 1.54/0.57    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 1.54/0.57    inference(negated_conjecture,[],[f13])).
% 1.54/0.57  fof(f13,conjecture,(
% 1.54/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).
% 1.54/0.57  fof(f85,plain,(
% 1.54/0.57    sK1 != k1_relat_1(sK3) | spl6_1),
% 1.54/0.57    inference(avatar_component_clause,[],[f83])).
% 1.54/0.57  fof(f83,plain,(
% 1.54/0.57    spl6_1 <=> sK1 = k1_relat_1(sK3)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.54/0.57  fof(f216,plain,(
% 1.54/0.57    ~spl6_4 | ~spl6_5 | spl6_6),
% 1.54/0.57    inference(avatar_contradiction_clause,[],[f214])).
% 1.54/0.57  fof(f214,plain,(
% 1.54/0.57    $false | (~spl6_4 | ~spl6_5 | spl6_6)),
% 1.54/0.57    inference(resolution,[],[f208,f193])).
% 1.54/0.57  fof(f193,plain,(
% 1.54/0.57    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl6_4 | ~spl6_5)),
% 1.54/0.57    inference(backward_demodulation,[],[f167,f183])).
% 1.54/0.57  fof(f167,plain,(
% 1.54/0.57    v1_funct_2(sK3,sK1,k1_xboole_0) | (~spl6_4 | ~spl6_5)),
% 1.54/0.57    inference(backward_demodulation,[],[f151,f148])).
% 1.54/0.57  fof(f151,plain,(
% 1.54/0.57    v1_funct_2(sK3,sK1,sK2) | ~spl6_5),
% 1.54/0.57    inference(avatar_component_clause,[],[f150])).
% 1.54/0.57  fof(f150,plain,(
% 1.54/0.57    spl6_5 <=> v1_funct_2(sK3,sK1,sK2)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.54/0.57  fof(f208,plain,(
% 1.54/0.57    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | spl6_6),
% 1.54/0.57    inference(avatar_component_clause,[],[f206])).
% 1.54/0.57  fof(f206,plain,(
% 1.54/0.57    spl6_6 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.54/0.57  fof(f213,plain,(
% 1.54/0.57    ~spl6_6 | spl6_7 | ~spl6_4),
% 1.54/0.57    inference(avatar_split_clause,[],[f204,f146,f210,f206])).
% 1.54/0.57  fof(f204,plain,(
% 1.54/0.57    k1_xboole_0 = k1_relat_1(sK3) | ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl6_4),
% 1.54/0.57    inference(forward_demodulation,[],[f202,f191])).
% 1.54/0.57  fof(f191,plain,(
% 1.54/0.57    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~spl6_4),
% 1.54/0.57    inference(backward_demodulation,[],[f160,f183])).
% 1.54/0.57  fof(f160,plain,(
% 1.54/0.57    k1_relat_1(sK3) = k1_relset_1(sK1,k1_xboole_0,sK3) | ~spl6_4),
% 1.54/0.57    inference(backward_demodulation,[],[f115,f148])).
% 1.54/0.57  fof(f115,plain,(
% 1.54/0.57    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 1.54/0.57    inference(resolution,[],[f112,f62])).
% 1.54/0.57  fof(f62,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f23])).
% 1.54/0.57  fof(f23,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(ennf_transformation,[],[f8])).
% 1.54/0.57  fof(f8,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.54/0.57  fof(f112,plain,(
% 1.54/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.54/0.57    inference(resolution,[],[f74,f72])).
% 1.54/0.57  fof(f74,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.54/0.57    inference(definition_unfolding,[],[f61,f51])).
% 1.54/0.57  fof(f61,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f22])).
% 1.54/0.57  fof(f22,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 1.54/0.57    inference(ennf_transformation,[],[f11])).
% 1.54/0.57  fof(f11,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 1.54/0.57  fof(f202,plain,(
% 1.54/0.57    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~spl6_4),
% 1.54/0.57    inference(resolution,[],[f192,f78])).
% 1.54/0.57  fof(f78,plain,(
% 1.54/0.57    ( ! [X2,X1] : (~sP0(k1_xboole_0,X1,X2) | ~v1_funct_2(X1,k1_xboole_0,X2) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1)) )),
% 1.54/0.57    inference(equality_resolution,[],[f66])).
% 1.54/0.57  fof(f66,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 != X0 | ~sP0(X0,X1,X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f41])).
% 1.54/0.57  fof(f41,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.54/0.57    inference(rectify,[],[f40])).
% 1.54/0.57  fof(f40,plain,(
% 1.54/0.57    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.54/0.57    inference(nnf_transformation,[],[f27])).
% 1.54/0.57  fof(f27,plain,(
% 1.54/0.57    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.54/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.54/0.57  fof(f192,plain,(
% 1.54/0.57    sP0(k1_xboole_0,sK3,k1_xboole_0) | ~spl6_4),
% 1.54/0.57    inference(backward_demodulation,[],[f161,f183])).
% 1.54/0.57  fof(f161,plain,(
% 1.54/0.57    sP0(sK1,sK3,k1_xboole_0) | ~spl6_4),
% 1.54/0.57    inference(backward_demodulation,[],[f116,f148])).
% 1.54/0.57  fof(f116,plain,(
% 1.54/0.57    sP0(sK1,sK3,sK2)),
% 1.54/0.57    inference(resolution,[],[f112,f69])).
% 1.54/0.57  fof(f69,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f42])).
% 1.54/0.57  fof(f42,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(nnf_transformation,[],[f28])).
% 1.54/0.57  fof(f28,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(definition_folding,[],[f26,f27])).
% 1.54/0.57  fof(f26,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(flattening,[],[f25])).
% 1.54/0.57  fof(f25,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(ennf_transformation,[],[f9])).
% 1.54/0.57  fof(f9,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.54/0.57  fof(f156,plain,(
% 1.54/0.57    spl6_5),
% 1.54/0.57    inference(avatar_contradiction_clause,[],[f155])).
% 1.54/0.57  fof(f155,plain,(
% 1.54/0.57    $false | spl6_5),
% 1.54/0.57    inference(resolution,[],[f154,f72])).
% 1.54/0.57  fof(f154,plain,(
% 1.54/0.57    ~r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) | spl6_5),
% 1.54/0.57    inference(resolution,[],[f152,f75])).
% 1.54/0.57  fof(f75,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) )),
% 1.54/0.57    inference(definition_unfolding,[],[f60,f51])).
% 1.54/0.57  fof(f60,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f22])).
% 1.54/0.57  fof(f152,plain,(
% 1.54/0.57    ~v1_funct_2(sK3,sK1,sK2) | spl6_5),
% 1.54/0.57    inference(avatar_component_clause,[],[f150])).
% 1.54/0.57  fof(f153,plain,(
% 1.54/0.57    spl6_4 | ~spl6_5 | spl6_1),
% 1.54/0.57    inference(avatar_split_clause,[],[f144,f83,f150,f146])).
% 1.54/0.57  fof(f144,plain,(
% 1.54/0.57    sK1 = k1_relat_1(sK3) | ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2),
% 1.54/0.57    inference(forward_demodulation,[],[f143,f115])).
% 1.54/0.57  fof(f143,plain,(
% 1.54/0.57    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 1.54/0.57    inference(resolution,[],[f65,f116])).
% 1.54/0.57  fof(f65,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.54/0.57    inference(cnf_transformation,[],[f41])).
% 1.54/0.57  fof(f126,plain,(
% 1.54/0.57    spl6_3),
% 1.54/0.57    inference(avatar_contradiction_clause,[],[f125])).
% 1.54/0.57  fof(f125,plain,(
% 1.54/0.57    $false | spl6_3),
% 1.54/0.57    inference(resolution,[],[f123,f43])).
% 1.54/0.57  fof(f43,plain,(
% 1.54/0.57    v1_relat_1(sK3)),
% 1.54/0.57    inference(cnf_transformation,[],[f30])).
% 1.54/0.57  fof(f123,plain,(
% 1.54/0.57    ~v1_relat_1(sK3) | spl6_3),
% 1.54/0.57    inference(avatar_component_clause,[],[f121])).
% 1.54/0.57  fof(f121,plain,(
% 1.54/0.57    spl6_3 <=> v1_relat_1(sK3)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.54/0.57  fof(f124,plain,(
% 1.54/0.57    ~spl6_3 | spl6_2),
% 1.54/0.57    inference(avatar_split_clause,[],[f119,f87,f121])).
% 1.54/0.57  fof(f87,plain,(
% 1.54/0.57    spl6_2 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.54/0.57  fof(f119,plain,(
% 1.54/0.57    r1_tarski(k2_relat_1(sK3),sK2) | ~v1_relat_1(sK3)),
% 1.54/0.57    inference(resolution,[],[f117,f52])).
% 1.54/0.57  fof(f52,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f35])).
% 1.54/0.57  fof(f35,plain,(
% 1.54/0.57    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.54/0.57    inference(nnf_transformation,[],[f17])).
% 1.54/0.57  fof(f17,plain,(
% 1.54/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.54/0.57    inference(ennf_transformation,[],[f6])).
% 1.54/0.57  fof(f6,axiom,(
% 1.54/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.54/0.57  fof(f117,plain,(
% 1.54/0.57    v5_relat_1(sK3,sK2)),
% 1.54/0.57    inference(resolution,[],[f112,f64])).
% 1.54/0.57  fof(f64,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f24])).
% 1.54/0.57  fof(f24,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(ennf_transformation,[],[f7])).
% 1.54/0.57  fof(f7,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.54/0.57  fof(f90,plain,(
% 1.54/0.57    ~spl6_1 | ~spl6_2),
% 1.54/0.57    inference(avatar_split_clause,[],[f46,f87,f83])).
% 1.54/0.57  fof(f46,plain,(
% 1.54/0.57    ~r1_tarski(k2_relat_1(sK3),sK2) | sK1 != k1_relat_1(sK3)),
% 1.54/0.57    inference(cnf_transformation,[],[f30])).
% 1.54/0.57  % SZS output end Proof for theBenchmark
% 1.54/0.57  % (32554)------------------------------
% 1.54/0.57  % (32554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (32554)Termination reason: Refutation
% 1.54/0.57  
% 1.54/0.57  % (32554)Memory used [KB]: 6268
% 1.54/0.57  % (32554)Time elapsed: 0.156 s
% 1.54/0.57  % (32554)------------------------------
% 1.54/0.57  % (32554)------------------------------
% 1.54/0.57  % (32559)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.54/0.57  % (32543)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.54/0.57  % (32559)Refutation not found, incomplete strategy% (32559)------------------------------
% 1.54/0.57  % (32559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (32559)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (32561)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.54/0.57  % (32544)Refutation not found, incomplete strategy% (32544)------------------------------
% 1.54/0.57  % (32544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (32544)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (32544)Memory used [KB]: 10746
% 1.54/0.57  % (32544)Time elapsed: 0.163 s
% 1.54/0.57  % (32544)------------------------------
% 1.54/0.57  % (32544)------------------------------
% 1.54/0.57  % (32560)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.54/0.58  % (32542)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.54/0.58  % (32547)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.54/0.58  % (32567)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.54/0.58  % (32566)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.54/0.58  % (32562)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.54/0.58  % (32557)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.54/0.58  % (32564)Refutation not found, incomplete strategy% (32564)------------------------------
% 1.54/0.58  % (32564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (32564)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.58  
% 1.54/0.58  % (32564)Memory used [KB]: 11001
% 1.54/0.58  % (32564)Time elapsed: 0.146 s
% 1.54/0.58  % (32564)------------------------------
% 1.54/0.58  % (32564)------------------------------
% 1.54/0.58  % (32568)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.54/0.58  % (32563)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.54/0.58  % (32550)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.54/0.59  % (32553)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.54/0.59  % (32552)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.54/0.59  % (32570)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.54/0.59  % (32552)Refutation not found, incomplete strategy% (32552)------------------------------
% 1.54/0.59  % (32552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.59  % (32552)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.59  
% 1.54/0.59  % (32552)Memory used [KB]: 10618
% 1.54/0.59  % (32552)Time elapsed: 0.161 s
% 1.54/0.59  % (32552)------------------------------
% 1.54/0.59  % (32552)------------------------------
% 1.54/0.59  % (32550)Refutation not found, incomplete strategy% (32550)------------------------------
% 1.54/0.59  % (32550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.59  % (32550)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.59  
% 1.54/0.59  % (32550)Memory used [KB]: 10746
% 1.54/0.59  % (32550)Time elapsed: 0.179 s
% 1.54/0.59  % (32550)------------------------------
% 1.54/0.59  % (32550)------------------------------
% 1.54/0.59  % (32541)Success in time 0.226 s
%------------------------------------------------------------------------------
