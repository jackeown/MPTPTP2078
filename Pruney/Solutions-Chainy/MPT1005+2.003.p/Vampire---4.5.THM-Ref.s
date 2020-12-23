%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 119 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  244 ( 310 expanded)
%              Number of equality atoms :   85 ( 102 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f104,f109,f119,f129,f162,f167,f174,f196,f201])).

fof(f201,plain,
    ( spl4_15
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl4_15
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f166,f195])).

fof(f195,plain,
    ( ! [X2,X0,X1] : k1_xboole_0 = k7_relset_1(X0,X1,k1_xboole_0,X2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl4_18
  <=> ! [X1,X0,X2] : k1_xboole_0 = k7_relset_1(X0,X1,k1_xboole_0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f166,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl4_15
  <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f196,plain,
    ( spl4_18
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f184,f172,f194])).

fof(f172,plain,
    ( spl4_16
  <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f184,plain,
    ( ! [X2,X0,X1] : k1_xboole_0 = k7_relset_1(X0,X1,k1_xboole_0,X2)
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f181,f173])).

fof(f173,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f172])).

fof(f181,plain,(
    ! [X2,X0,X1] : k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
    inference(resolution,[],[f59,f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f174,plain,
    ( spl4_16
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f169,f160,f172])).

fof(f160,plain,
    ( spl4_14
  <=> ! [X0] : r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f169,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f168,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f168,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,X0))
        | k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) )
    | ~ spl4_14 ),
    inference(resolution,[],[f161,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f161,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f160])).

fof(f167,plain,
    ( ~ spl4_15
    | spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f140,f116,f106,f164])).

fof(f106,plain,
    ( spl4_8
  <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f116,plain,
    ( spl4_9
  <=> r2_hidden(sK2,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f140,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl4_8
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f108,f135])).

fof(f135,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_9 ),
    inference(resolution,[],[f118,f64])).

fof(f64,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f118,plain,
    ( r2_hidden(sK2,k1_tarski(k1_xboole_0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f108,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f162,plain,
    ( spl4_14
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f133,f126,f83,f160])).

fof(f83,plain,
    ( spl4_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f126,plain,
    ( spl4_10
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f133,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f132,f85])).

fof(f85,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f132,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0))
    | ~ spl4_10 ),
    inference(resolution,[],[f128,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f128,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f129,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f120,f126])).

fof(f120,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f57,f44])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f119,plain,
    ( spl4_9
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f114,f101,f116])).

fof(f101,plain,
    ( spl4_7
  <=> m1_subset_1(sK2,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f114,plain,
    ( r2_hidden(sK2,k1_tarski(k1_xboole_0))
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f113,f42])).

fof(f42,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f113,plain,
    ( v1_xboole_0(k1_tarski(k1_xboole_0))
    | r2_hidden(sK2,k1_tarski(k1_xboole_0))
    | ~ spl4_7 ),
    inference(resolution,[],[f46,f103])).

fof(f103,plain,
    ( m1_subset_1(sK2,k1_tarski(k1_xboole_0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f109,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f38,f106])).

fof(f38,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    & v1_funct_2(sK2,k1_xboole_0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
   => ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
      & v1_funct_2(sK2,k1_xboole_0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).

fof(f104,plain,
    ( spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f99,f88,f101])).

fof(f88,plain,
    ( spl4_5
  <=> k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f99,plain,
    ( m1_subset_1(sK2,k1_tarski(k1_xboole_0))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f98,f90])).

fof(f90,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f98,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f37,f66])).

fof(f66,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f39,f88])).

fof(f39,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f86,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f41,f83])).

fof(f41,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:54:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (16918)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (16921)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (16921)Refutation not found, incomplete strategy% (16921)------------------------------
% 0.22/0.51  % (16921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (16921)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (16921)Memory used [KB]: 6140
% 0.22/0.51  % (16921)Time elapsed: 0.071 s
% 0.22/0.51  % (16921)------------------------------
% 0.22/0.51  % (16921)------------------------------
% 0.22/0.51  % (16918)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f202,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f86,f91,f104,f109,f119,f129,f162,f167,f174,f196,f201])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    spl4_15 | ~spl4_18),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f197])).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    $false | (spl4_15 | ~spl4_18)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f166,f195])).
% 0.22/0.51  fof(f195,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relset_1(X0,X1,k1_xboole_0,X2)) ) | ~spl4_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f194])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    spl4_18 <=> ! [X1,X0,X2] : k1_xboole_0 = k7_relset_1(X0,X1,k1_xboole_0,X2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | spl4_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f164])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    spl4_15 <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.51  fof(f196,plain,(
% 0.22/0.51    spl4_18 | ~spl4_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f184,f172,f194])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    spl4_16 <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relset_1(X0,X1,k1_xboole_0,X2)) ) | ~spl4_16),
% 0.22/0.51    inference(forward_demodulation,[],[f181,f173])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | ~spl4_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f172])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2)) )),
% 0.22/0.51    inference(resolution,[],[f59,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    spl4_16 | ~spl4_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f169,f160,f172])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    spl4_14 <=> ! [X0] : r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | ~spl4_14),
% 0.22/0.51    inference(subsumption_resolution,[],[f168,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) | k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | ~spl4_14),
% 0.22/0.51    inference(resolution,[],[f161,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl4_14),
% 0.22/0.51    inference(avatar_component_clause,[],[f160])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    ~spl4_15 | spl4_8 | ~spl4_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f140,f116,f106,f164])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    spl4_8 <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    spl4_9 <=> r2_hidden(sK2,k1_tarski(k1_xboole_0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | (spl4_8 | ~spl4_9)),
% 0.22/0.51    inference(backward_demodulation,[],[f108,f135])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | ~spl4_9),
% 0.22/0.51    inference(resolution,[],[f118,f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.22/0.51    inference(equality_resolution,[],[f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.51    inference(rectify,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    r2_hidden(sK2,k1_tarski(k1_xboole_0)) | ~spl4_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f116])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl4_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f106])).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    spl4_14 | ~spl4_4 | ~spl4_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f133,f126,f83,f160])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    spl4_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    spl4_10 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | (~spl4_4 | ~spl4_10)),
% 0.22/0.51    inference(forward_demodulation,[],[f132,f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl4_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f83])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k9_relat_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0))) ) | ~spl4_10),
% 0.22/0.51    inference(resolution,[],[f128,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    v1_relat_1(k1_xboole_0) | ~spl4_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f126])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    spl4_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f120,f126])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    v1_relat_1(k1_xboole_0)),
% 0.22/0.51    inference(resolution,[],[f57,f44])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    spl4_9 | ~spl4_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f114,f101,f116])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    spl4_7 <=> m1_subset_1(sK2,k1_tarski(k1_xboole_0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    r2_hidden(sK2,k1_tarski(k1_xboole_0)) | ~spl4_7),
% 0.22/0.51    inference(subsumption_resolution,[],[f113,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    v1_xboole_0(k1_tarski(k1_xboole_0)) | r2_hidden(sK2,k1_tarski(k1_xboole_0)) | ~spl4_7),
% 0.22/0.51    inference(resolution,[],[f46,f103])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_tarski(k1_xboole_0)) | ~spl4_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f101])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ~spl4_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f38,f106])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => (k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.51    inference(negated_conjecture,[],[f14])).
% 0.22/0.51  fof(f14,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    spl4_7 | ~spl4_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f99,f88,f101])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    spl4_5 <=> k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_tarski(k1_xboole_0)) | ~spl4_5),
% 0.22/0.51    inference(forward_demodulation,[],[f98,f90])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) | ~spl4_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f88])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.51    inference(forward_demodulation,[],[f37,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.51    inference(flattening,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    spl4_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f39,f88])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    spl4_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f41,f83])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (16918)------------------------------
% 0.22/0.51  % (16918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (16918)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (16918)Memory used [KB]: 6268
% 0.22/0.51  % (16918)Time elapsed: 0.076 s
% 0.22/0.51  % (16918)------------------------------
% 0.22/0.51  % (16918)------------------------------
% 0.22/0.52  % (16915)Success in time 0.151 s
%------------------------------------------------------------------------------
