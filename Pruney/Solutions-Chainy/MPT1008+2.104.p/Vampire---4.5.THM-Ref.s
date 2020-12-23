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
% DateTime   : Thu Dec  3 13:04:23 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 193 expanded)
%              Number of leaves         :   27 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  358 ( 593 expanded)
%              Number of equality atoms :  145 ( 246 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f205,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f90,f95,f100,f105,f115,f119,f129,f140,f161,f174,f186,f198,f204])).

fof(f204,plain,
    ( ~ spl4_12
    | spl4_14
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl4_12
    | spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f173,f201])).

fof(f201,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | spl4_14
    | ~ spl4_15 ),
    inference(trivial_inequality_removal,[],[f200])).

fof(f200,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | spl4_14
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f189,f197])).

fof(f197,plain,
    ( k2_relat_1(sK2) = k11_relat_1(sK2,sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl4_15
  <=> k2_relat_1(sK2) = k11_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f189,plain,
    ( k2_relat_1(sK2) != k11_relat_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | spl4_14 ),
    inference(superposition,[],[f185,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f185,plain,
    ( k11_relat_1(sK2,sK0) != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl4_14
  <=> k11_relat_1(sK2,sK0) = k2_relset_1(k1_relat_1(sK2),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f173,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl4_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f198,plain,
    ( ~ spl4_7
    | spl4_15
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f192,f137,f195,f112])).

fof(f112,plain,
    ( spl4_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f137,plain,
    ( spl4_9
  <=> k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f192,plain,
    ( k2_relat_1(sK2) = k11_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,
    ( k2_relat_1(sK2) = k11_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_9 ),
    inference(superposition,[],[f57,f147])).

fof(f147,plain,
    ( ! [X1] :
        ( k11_relat_1(X1,sK0) = k9_relat_1(X1,k1_relat_1(sK2))
        | ~ v1_relat_1(X1) )
    | ~ spl4_9 ),
    inference(superposition,[],[f64,f139])).

fof(f139,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f137])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f59])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f57,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f186,plain,
    ( ~ spl4_7
    | ~ spl4_1
    | ~ spl4_10
    | ~ spl4_14
    | spl4_5
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f160,f137,f102,f183,f150,f82,f112])).

fof(f82,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f150,plain,
    ( spl4_10
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f102,plain,
    ( spl4_5
  <=> k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) = k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f160,plain,
    ( k11_relat_1(sK2,sK0) != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_5
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f154,f139])).

fof(f154,plain,
    ( k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) != k11_relat_1(sK2,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_5 ),
    inference(superposition,[],[f104,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f38,f59])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f104,plain,
    ( k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) != k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f174,plain,
    ( spl4_12
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f142,f137,f97,f171])).

fof(f97,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f142,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(superposition,[],[f99,f139])).

fof(f99,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f161,plain,
    ( spl4_10
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f146,f137,f150])).

fof(f146,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl4_9 ),
    inference(superposition,[],[f77,f139])).

fof(f77,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f53,f58])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f140,plain,
    ( ~ spl4_4
    | spl4_9
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f132,f126,f137,f97])).

fof(f126,plain,
    ( spl4_8
  <=> k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f132,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | ~ spl4_8 ),
    inference(superposition,[],[f128,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f128,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f129,plain,
    ( spl4_8
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f124,f97,f92,f87,f126])).

fof(f87,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f92,plain,
    ( spl4_3
  <=> v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f124,plain,
    ( ~ v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1)
    | k1_xboole_0 = sK1
    | k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f40,f99])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

% (9647)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f119,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f48,f110])).

fof(f110,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_6
  <=> v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f115,plain,
    ( ~ spl4_6
    | spl4_7
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f106,f97,f112,f108])).

fof(f106,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f47,f99])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f105,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f60,f102])).

fof(f60,plain,(
    k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) != k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f37,f59,f59])).

fof(f37,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f100,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f61,f97])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f35,f59])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f95,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f62,f92])).

fof(f62,plain,(
    v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f34,f59])).

fof(f34,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f90,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f36,f87])).

fof(f36,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f33,f82])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:21:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (9665)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (9657)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (9649)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.24/0.53  % (9665)Refutation found. Thanks to Tanya!
% 1.24/0.53  % SZS status Theorem for theBenchmark
% 1.24/0.53  % SZS output start Proof for theBenchmark
% 1.24/0.53  fof(f205,plain,(
% 1.24/0.53    $false),
% 1.24/0.53    inference(avatar_sat_refutation,[],[f85,f90,f95,f100,f105,f115,f119,f129,f140,f161,f174,f186,f198,f204])).
% 1.24/0.53  fof(f204,plain,(
% 1.24/0.53    ~spl4_12 | spl4_14 | ~spl4_15),
% 1.24/0.53    inference(avatar_contradiction_clause,[],[f202])).
% 1.24/0.53  fof(f202,plain,(
% 1.24/0.53    $false | (~spl4_12 | spl4_14 | ~spl4_15)),
% 1.24/0.53    inference(subsumption_resolution,[],[f173,f201])).
% 1.24/0.53  fof(f201,plain,(
% 1.24/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | (spl4_14 | ~spl4_15)),
% 1.24/0.53    inference(trivial_inequality_removal,[],[f200])).
% 1.24/0.53  fof(f200,plain,(
% 1.24/0.53    k2_relat_1(sK2) != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | (spl4_14 | ~spl4_15)),
% 1.24/0.53    inference(forward_demodulation,[],[f189,f197])).
% 1.24/0.53  fof(f197,plain,(
% 1.24/0.53    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) | ~spl4_15),
% 1.24/0.53    inference(avatar_component_clause,[],[f195])).
% 1.24/0.53  fof(f195,plain,(
% 1.24/0.53    spl4_15 <=> k2_relat_1(sK2) = k11_relat_1(sK2,sK0)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.24/0.53  fof(f189,plain,(
% 1.24/0.53    k2_relat_1(sK2) != k11_relat_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | spl4_14),
% 1.24/0.53    inference(superposition,[],[f185,f39])).
% 1.24/0.53  fof(f39,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f18])).
% 1.24/0.53  fof(f18,plain,(
% 1.24/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.53    inference(ennf_transformation,[],[f10])).
% 1.24/0.53  fof(f10,axiom,(
% 1.24/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.24/0.53  fof(f185,plain,(
% 1.24/0.53    k11_relat_1(sK2,sK0) != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | spl4_14),
% 1.24/0.53    inference(avatar_component_clause,[],[f183])).
% 1.24/0.53  fof(f183,plain,(
% 1.24/0.53    spl4_14 <=> k11_relat_1(sK2,sK0) = k2_relset_1(k1_relat_1(sK2),sK1,sK2)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.24/0.53  fof(f173,plain,(
% 1.24/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~spl4_12),
% 1.24/0.53    inference(avatar_component_clause,[],[f171])).
% 1.24/0.53  fof(f171,plain,(
% 1.24/0.53    spl4_12 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.24/0.53  fof(f198,plain,(
% 1.24/0.53    ~spl4_7 | spl4_15 | ~spl4_9),
% 1.24/0.53    inference(avatar_split_clause,[],[f192,f137,f195,f112])).
% 1.24/0.53  fof(f112,plain,(
% 1.24/0.53    spl4_7 <=> v1_relat_1(sK2)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.24/0.53  fof(f137,plain,(
% 1.24/0.53    spl4_9 <=> k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.24/0.53  fof(f192,plain,(
% 1.24/0.53    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | ~spl4_9),
% 1.24/0.53    inference(duplicate_literal_removal,[],[f191])).
% 1.24/0.53  fof(f191,plain,(
% 1.24/0.53    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl4_9),
% 1.24/0.53    inference(superposition,[],[f57,f147])).
% 1.24/0.53  fof(f147,plain,(
% 1.24/0.53    ( ! [X1] : (k11_relat_1(X1,sK0) = k9_relat_1(X1,k1_relat_1(sK2)) | ~v1_relat_1(X1)) ) | ~spl4_9),
% 1.24/0.53    inference(superposition,[],[f64,f139])).
% 1.24/0.53  fof(f139,plain,(
% 1.24/0.53    k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2) | ~spl4_9),
% 1.24/0.53    inference(avatar_component_clause,[],[f137])).
% 1.24/0.53  fof(f64,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 1.24/0.53    inference(definition_unfolding,[],[f49,f59])).
% 1.24/0.53  fof(f59,plain,(
% 1.24/0.53    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.24/0.53    inference(definition_unfolding,[],[f50,f58])).
% 1.24/0.53  fof(f58,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f3])).
% 1.24/0.53  fof(f3,axiom,(
% 1.24/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.24/0.53  fof(f50,plain,(
% 1.24/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f2])).
% 1.24/0.53  fof(f2,axiom,(
% 1.24/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.24/0.53  fof(f49,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f23])).
% 1.24/0.53  fof(f23,plain,(
% 1.24/0.53    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.24/0.53    inference(ennf_transformation,[],[f5])).
% 1.24/0.53  fof(f5,axiom,(
% 1.24/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 1.24/0.53  fof(f57,plain,(
% 1.24/0.53    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f24])).
% 1.24/0.53  fof(f24,plain,(
% 1.24/0.53    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.24/0.53    inference(ennf_transformation,[],[f7])).
% 1.24/0.53  fof(f7,axiom,(
% 1.24/0.53    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.24/0.53  fof(f186,plain,(
% 1.24/0.53    ~spl4_7 | ~spl4_1 | ~spl4_10 | ~spl4_14 | spl4_5 | ~spl4_9),
% 1.24/0.53    inference(avatar_split_clause,[],[f160,f137,f102,f183,f150,f82,f112])).
% 1.24/0.53  fof(f82,plain,(
% 1.24/0.53    spl4_1 <=> v1_funct_1(sK2)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.24/0.53  fof(f150,plain,(
% 1.24/0.53    spl4_10 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.24/0.53  fof(f102,plain,(
% 1.24/0.53    spl4_5 <=> k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) = k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.24/0.53  fof(f160,plain,(
% 1.24/0.53    k11_relat_1(sK2,sK0) != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_5 | ~spl4_9)),
% 1.24/0.53    inference(forward_demodulation,[],[f154,f139])).
% 1.24/0.53  fof(f154,plain,(
% 1.24/0.53    k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) != k11_relat_1(sK2,sK0) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_5),
% 1.24/0.53    inference(superposition,[],[f104,f63])).
% 1.24/0.53  fof(f63,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.24/0.53    inference(definition_unfolding,[],[f38,f59])).
% 1.24/0.53  fof(f38,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f17])).
% 1.24/0.53  fof(f17,plain,(
% 1.24/0.53    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.24/0.53    inference(flattening,[],[f16])).
% 1.24/0.53  fof(f16,plain,(
% 1.24/0.53    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.24/0.53    inference(ennf_transformation,[],[f8])).
% 1.24/0.53  fof(f8,axiom,(
% 1.24/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 1.24/0.53  fof(f104,plain,(
% 1.24/0.53    k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) != k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) | spl4_5),
% 1.24/0.53    inference(avatar_component_clause,[],[f102])).
% 1.24/0.53  fof(f174,plain,(
% 1.24/0.53    spl4_12 | ~spl4_4 | ~spl4_9),
% 1.24/0.53    inference(avatar_split_clause,[],[f142,f137,f97,f171])).
% 1.24/0.53  fof(f97,plain,(
% 1.24/0.53    spl4_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.24/0.53  fof(f142,plain,(
% 1.24/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | (~spl4_4 | ~spl4_9)),
% 1.24/0.53    inference(superposition,[],[f99,f139])).
% 1.24/0.53  fof(f99,plain,(
% 1.24/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) | ~spl4_4),
% 1.24/0.53    inference(avatar_component_clause,[],[f97])).
% 1.24/0.53  fof(f161,plain,(
% 1.24/0.53    spl4_10 | ~spl4_9),
% 1.24/0.53    inference(avatar_split_clause,[],[f146,f137,f150])).
% 1.24/0.53  fof(f146,plain,(
% 1.24/0.53    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl4_9),
% 1.24/0.53    inference(superposition,[],[f77,f139])).
% 1.24/0.53  fof(f77,plain,(
% 1.24/0.53    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 1.24/0.53    inference(equality_resolution,[],[f76])).
% 1.24/0.53  fof(f76,plain,(
% 1.24/0.53    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 1.24/0.53    inference(equality_resolution,[],[f68])).
% 1.24/0.53  fof(f68,plain,(
% 1.24/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 1.24/0.53    inference(definition_unfolding,[],[f53,f58])).
% 1.24/0.53  fof(f53,plain,(
% 1.24/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.24/0.53    inference(cnf_transformation,[],[f32])).
% 1.24/0.53  fof(f32,plain,(
% 1.24/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 1.24/0.53  fof(f31,plain,(
% 1.24/0.53    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f30,plain,(
% 1.24/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.24/0.53    inference(rectify,[],[f29])).
% 1.24/0.53  fof(f29,plain,(
% 1.24/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.24/0.53    inference(flattening,[],[f28])).
% 1.24/0.53  fof(f28,plain,(
% 1.24/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.24/0.53    inference(nnf_transformation,[],[f1])).
% 1.24/0.53  fof(f1,axiom,(
% 1.24/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.24/0.53  fof(f140,plain,(
% 1.24/0.53    ~spl4_4 | spl4_9 | ~spl4_8),
% 1.24/0.53    inference(avatar_split_clause,[],[f132,f126,f137,f97])).
% 1.24/0.53  fof(f126,plain,(
% 1.24/0.53    spl4_8 <=> k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.24/0.53  fof(f132,plain,(
% 1.24/0.53    k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) | ~spl4_8),
% 1.24/0.53    inference(superposition,[],[f128,f46])).
% 1.24/0.53  fof(f46,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f21])).
% 1.24/0.53  fof(f21,plain,(
% 1.24/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.53    inference(ennf_transformation,[],[f9])).
% 1.24/0.53  fof(f9,axiom,(
% 1.24/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.24/0.53  fof(f128,plain,(
% 1.24/0.53    k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) | ~spl4_8),
% 1.24/0.53    inference(avatar_component_clause,[],[f126])).
% 1.24/0.53  fof(f129,plain,(
% 1.24/0.53    spl4_8 | spl4_2 | ~spl4_3 | ~spl4_4),
% 1.24/0.53    inference(avatar_split_clause,[],[f124,f97,f92,f87,f126])).
% 1.24/0.53  fof(f87,plain,(
% 1.24/0.53    spl4_2 <=> k1_xboole_0 = sK1),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.24/0.53  fof(f92,plain,(
% 1.24/0.53    spl4_3 <=> v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.24/0.53  fof(f124,plain,(
% 1.24/0.53    ~v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1) | k1_xboole_0 = sK1 | k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) | ~spl4_4),
% 1.24/0.53    inference(resolution,[],[f40,f99])).
% 1.24/0.53  fof(f40,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.24/0.53    inference(cnf_transformation,[],[f27])).
% 1.24/0.53  fof(f27,plain,(
% 1.24/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.53    inference(nnf_transformation,[],[f20])).
% 1.24/0.53  fof(f20,plain,(
% 1.24/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.53    inference(flattening,[],[f19])).
% 1.24/0.53  fof(f19,plain,(
% 1.24/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.53    inference(ennf_transformation,[],[f11])).
% 1.24/0.53  fof(f11,axiom,(
% 1.24/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.24/0.53  % (9647)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.24/0.53  fof(f119,plain,(
% 1.24/0.53    spl4_6),
% 1.24/0.53    inference(avatar_contradiction_clause,[],[f116])).
% 1.24/0.53  fof(f116,plain,(
% 1.24/0.53    $false | spl4_6),
% 1.24/0.53    inference(unit_resulting_resolution,[],[f48,f110])).
% 1.24/0.53  fof(f110,plain,(
% 1.24/0.53    ~v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) | spl4_6),
% 1.24/0.53    inference(avatar_component_clause,[],[f108])).
% 1.24/0.53  fof(f108,plain,(
% 1.24/0.53    spl4_6 <=> v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.24/0.53  fof(f48,plain,(
% 1.24/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f6])).
% 1.24/0.53  fof(f6,axiom,(
% 1.24/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.24/0.53  fof(f115,plain,(
% 1.24/0.53    ~spl4_6 | spl4_7 | ~spl4_4),
% 1.24/0.53    inference(avatar_split_clause,[],[f106,f97,f112,f108])).
% 1.24/0.53  fof(f106,plain,(
% 1.24/0.53    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) | ~spl4_4),
% 1.24/0.53    inference(resolution,[],[f47,f99])).
% 1.24/0.53  fof(f47,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f22])).
% 1.24/0.53  fof(f22,plain,(
% 1.24/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.24/0.53    inference(ennf_transformation,[],[f4])).
% 1.24/0.53  fof(f4,axiom,(
% 1.24/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.24/0.53  fof(f105,plain,(
% 1.24/0.53    ~spl4_5),
% 1.24/0.53    inference(avatar_split_clause,[],[f60,f102])).
% 1.24/0.53  fof(f60,plain,(
% 1.24/0.53    k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) != k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 1.24/0.53    inference(definition_unfolding,[],[f37,f59,f59])).
% 1.24/0.53  fof(f37,plain,(
% 1.24/0.53    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 1.24/0.53    inference(cnf_transformation,[],[f26])).
% 1.24/0.53  fof(f26,plain,(
% 1.24/0.53    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 1.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f25])).
% 1.24/0.53  fof(f25,plain,(
% 1.24/0.53    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f15,plain,(
% 1.24/0.53    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.24/0.53    inference(flattening,[],[f14])).
% 1.24/0.53  fof(f14,plain,(
% 1.24/0.53    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.24/0.53    inference(ennf_transformation,[],[f13])).
% 1.24/0.53  fof(f13,negated_conjecture,(
% 1.24/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.24/0.53    inference(negated_conjecture,[],[f12])).
% 1.24/0.53  fof(f12,conjecture,(
% 1.24/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 1.24/0.53  fof(f100,plain,(
% 1.24/0.53    spl4_4),
% 1.24/0.53    inference(avatar_split_clause,[],[f61,f97])).
% 1.24/0.53  fof(f61,plain,(
% 1.24/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 1.24/0.53    inference(definition_unfolding,[],[f35,f59])).
% 1.24/0.53  fof(f35,plain,(
% 1.24/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.24/0.53    inference(cnf_transformation,[],[f26])).
% 1.24/0.53  fof(f95,plain,(
% 1.24/0.53    spl4_3),
% 1.24/0.53    inference(avatar_split_clause,[],[f62,f92])).
% 1.24/0.53  fof(f62,plain,(
% 1.24/0.53    v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1)),
% 1.24/0.53    inference(definition_unfolding,[],[f34,f59])).
% 1.24/0.53  fof(f34,plain,(
% 1.24/0.53    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.24/0.53    inference(cnf_transformation,[],[f26])).
% 1.24/0.53  fof(f90,plain,(
% 1.24/0.53    ~spl4_2),
% 1.24/0.53    inference(avatar_split_clause,[],[f36,f87])).
% 1.24/0.53  fof(f36,plain,(
% 1.24/0.53    k1_xboole_0 != sK1),
% 1.24/0.53    inference(cnf_transformation,[],[f26])).
% 1.24/0.53  fof(f85,plain,(
% 1.24/0.53    spl4_1),
% 1.24/0.53    inference(avatar_split_clause,[],[f33,f82])).
% 1.24/0.53  fof(f33,plain,(
% 1.24/0.53    v1_funct_1(sK2)),
% 1.24/0.53    inference(cnf_transformation,[],[f26])).
% 1.24/0.53  % SZS output end Proof for theBenchmark
% 1.24/0.53  % (9665)------------------------------
% 1.24/0.53  % (9665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (9665)Termination reason: Refutation
% 1.24/0.53  
% 1.24/0.53  % (9665)Memory used [KB]: 10874
% 1.24/0.53  % (9665)Time elapsed: 0.070 s
% 1.24/0.53  % (9665)------------------------------
% 1.24/0.53  % (9665)------------------------------
% 1.24/0.53  % (9641)Success in time 0.17 s
%------------------------------------------------------------------------------
