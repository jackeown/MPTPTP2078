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
% DateTime   : Thu Dec  3 13:04:03 EST 2020

% Result     : Theorem 0.88s
% Output     : Refutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 177 expanded)
%              Number of leaves         :   20 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  308 ( 631 expanded)
%              Number of equality atoms :  109 ( 192 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f152,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f115,f117,f148,f151])).

fof(f151,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f102,f122])).

fof(f122,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f119,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f119,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(global_subsumption,[],[f70,f118])).

fof(f118,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(superposition,[],[f56,f106])).

fof(f106,plain,(
    k2_relat_1(sK2) = k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) ),
    inference(resolution,[],[f70,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f41,f69])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f102,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_3
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f148,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f99,f137])).

fof(f137,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(superposition,[],[f86,f121])).

fof(f121,plain,(
    k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f110,f107])).

fof(f107,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) ),
    inference(resolution,[],[f70,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f110,plain,(
    k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) ),
    inference(global_subsumption,[],[f42,f71,f104])).

fof(f104,plain,
    ( ~ v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1)
    | k1_xboole_0 = sK1
    | k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) ),
    inference(resolution,[],[f70,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f25])).

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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f71,plain,(
    v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f40,f69])).

fof(f40,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f86,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f64,f47])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f99,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl5_2
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f117,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f113,f46])).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f113,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_4
  <=> v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f115,plain,
    ( ~ spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f109,f95,f112])).

fof(f95,plain,
    ( spl5_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f109,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    inference(resolution,[],[f70,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f103,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f93,f101,f98,f95])).

fof(f93,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(global_subsumption,[],[f39,f89])).

fof(f89,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f88,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f88,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_funct_1(sK2,sK0),X0)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f43,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f43,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (741736448)
% 0.13/0.37  ipcrm: permission denied for id (741769219)
% 0.13/0.37  ipcrm: permission denied for id (741801988)
% 0.13/0.37  ipcrm: permission denied for id (741867526)
% 0.13/0.37  ipcrm: permission denied for id (741933065)
% 0.13/0.38  ipcrm: permission denied for id (741998603)
% 0.13/0.38  ipcrm: permission denied for id (742096911)
% 0.13/0.39  ipcrm: permission denied for id (742129682)
% 0.13/0.39  ipcrm: permission denied for id (742195220)
% 0.13/0.39  ipcrm: permission denied for id (742227989)
% 0.13/0.39  ipcrm: permission denied for id (742293528)
% 0.13/0.40  ipcrm: permission denied for id (742359068)
% 0.13/0.40  ipcrm: permission denied for id (742457377)
% 0.13/0.41  ipcrm: permission denied for id (742522916)
% 0.13/0.42  ipcrm: permission denied for id (742785070)
% 0.13/0.42  ipcrm: permission denied for id (742817841)
% 0.20/0.43  ipcrm: permission denied for id (743014460)
% 0.20/0.44  ipcrm: permission denied for id (743047230)
% 0.20/0.44  ipcrm: permission denied for id (743079999)
% 0.20/0.44  ipcrm: permission denied for id (743145538)
% 0.20/0.44  ipcrm: permission denied for id (743178307)
% 0.20/0.44  ipcrm: permission denied for id (743211076)
% 0.20/0.45  ipcrm: permission denied for id (743243845)
% 0.20/0.45  ipcrm: permission denied for id (743309385)
% 0.20/0.45  ipcrm: permission denied for id (743342155)
% 0.20/0.45  ipcrm: permission denied for id (743374925)
% 0.20/0.47  ipcrm: permission denied for id (743538775)
% 0.20/0.48  ipcrm: permission denied for id (743637087)
% 0.20/0.48  ipcrm: permission denied for id (743669856)
% 0.20/0.48  ipcrm: permission denied for id (743768164)
% 0.20/0.49  ipcrm: permission denied for id (743899242)
% 0.20/0.49  ipcrm: permission denied for id (743932012)
% 0.20/0.50  ipcrm: permission denied for id (744030322)
% 0.20/0.50  ipcrm: permission denied for id (744063091)
% 0.20/0.50  ipcrm: permission denied for id (744095860)
% 0.20/0.50  ipcrm: permission denied for id (744128629)
% 0.20/0.50  ipcrm: permission denied for id (744161399)
% 0.20/0.50  ipcrm: permission denied for id (744194168)
% 0.20/0.51  ipcrm: permission denied for id (744226938)
% 0.20/0.51  ipcrm: permission denied for id (744259707)
% 0.88/0.65  % (18506)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.88/0.65  % (18491)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.88/0.66  % (18491)Refutation found. Thanks to Tanya!
% 0.88/0.66  % SZS status Theorem for theBenchmark
% 0.88/0.66  % SZS output start Proof for theBenchmark
% 0.88/0.66  fof(f152,plain,(
% 0.88/0.66    $false),
% 0.88/0.66    inference(avatar_sat_refutation,[],[f103,f115,f117,f148,f151])).
% 0.88/0.66  fof(f151,plain,(
% 0.88/0.66    spl5_3),
% 0.88/0.66    inference(avatar_contradiction_clause,[],[f150])).
% 0.88/0.66  fof(f150,plain,(
% 0.88/0.66    $false | spl5_3),
% 0.88/0.66    inference(subsumption_resolution,[],[f102,f122])).
% 0.88/0.66  fof(f122,plain,(
% 0.88/0.66    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.88/0.66    inference(resolution,[],[f119,f52])).
% 0.88/0.66  fof(f52,plain,(
% 0.88/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.88/0.66    inference(cnf_transformation,[],[f32])).
% 0.88/0.66  fof(f32,plain,(
% 0.88/0.66    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.88/0.66    inference(nnf_transformation,[],[f5])).
% 0.88/0.66  fof(f5,axiom,(
% 0.88/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.88/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.88/0.66  fof(f119,plain,(
% 0.88/0.66    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.88/0.66    inference(global_subsumption,[],[f70,f118])).
% 0.88/0.66  fof(f118,plain,(
% 0.88/0.66    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 0.88/0.66    inference(superposition,[],[f56,f106])).
% 0.88/0.66  fof(f106,plain,(
% 0.88/0.66    k2_relat_1(sK2) = k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2)),
% 0.88/0.66    inference(resolution,[],[f70,f55])).
% 0.88/0.66  fof(f55,plain,(
% 0.88/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.88/0.66    inference(cnf_transformation,[],[f22])).
% 0.88/0.66  fof(f22,plain,(
% 0.88/0.66    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.88/0.66    inference(ennf_transformation,[],[f11])).
% 0.88/0.66  fof(f11,axiom,(
% 0.88/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.88/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.88/0.66  fof(f56,plain,(
% 0.88/0.66    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.88/0.66    inference(cnf_transformation,[],[f23])).
% 0.88/0.66  fof(f23,plain,(
% 0.88/0.66    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.88/0.66    inference(ennf_transformation,[],[f9])).
% 0.88/0.66  fof(f9,axiom,(
% 0.88/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.88/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.88/0.66  fof(f70,plain,(
% 0.88/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 0.88/0.66    inference(definition_unfolding,[],[f41,f69])).
% 0.88/0.66  fof(f69,plain,(
% 0.88/0.66    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.88/0.66    inference(definition_unfolding,[],[f44,f47])).
% 0.88/0.66  fof(f47,plain,(
% 0.88/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.88/0.66    inference(cnf_transformation,[],[f4])).
% 0.88/0.66  fof(f4,axiom,(
% 0.88/0.66    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.88/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.88/0.66  fof(f44,plain,(
% 0.88/0.66    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.88/0.66    inference(cnf_transformation,[],[f3])).
% 0.88/0.66  fof(f3,axiom,(
% 0.88/0.66    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.88/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.88/0.66  fof(f41,plain,(
% 0.88/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.88/0.66    inference(cnf_transformation,[],[f27])).
% 0.88/0.66  fof(f27,plain,(
% 0.88/0.66    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.88/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f26])).
% 0.88/0.66  fof(f26,plain,(
% 0.88/0.66    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.88/0.66    introduced(choice_axiom,[])).
% 0.88/0.66  fof(f16,plain,(
% 0.88/0.66    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.88/0.66    inference(flattening,[],[f15])).
% 0.88/0.66  fof(f15,plain,(
% 0.88/0.66    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.88/0.66    inference(ennf_transformation,[],[f14])).
% 0.88/0.66  fof(f14,negated_conjecture,(
% 0.88/0.66    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.88/0.66    inference(negated_conjecture,[],[f13])).
% 0.88/0.66  fof(f13,conjecture,(
% 0.88/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.88/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 0.88/0.66  fof(f102,plain,(
% 0.88/0.66    ~r1_tarski(k2_relat_1(sK2),sK1) | spl5_3),
% 0.88/0.66    inference(avatar_component_clause,[],[f101])).
% 0.88/0.66  fof(f101,plain,(
% 0.88/0.66    spl5_3 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.88/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.88/0.66  fof(f148,plain,(
% 0.88/0.66    spl5_2),
% 0.88/0.66    inference(avatar_contradiction_clause,[],[f147])).
% 0.88/0.66  fof(f147,plain,(
% 0.88/0.66    $false | spl5_2),
% 0.88/0.66    inference(subsumption_resolution,[],[f99,f137])).
% 0.88/0.66  fof(f137,plain,(
% 0.88/0.66    r2_hidden(sK0,k1_relat_1(sK2))),
% 0.88/0.66    inference(superposition,[],[f86,f121])).
% 0.88/0.66  fof(f121,plain,(
% 0.88/0.66    k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2)),
% 0.88/0.66    inference(forward_demodulation,[],[f110,f107])).
% 0.88/0.66  fof(f107,plain,(
% 0.88/0.66    k1_relat_1(sK2) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2)),
% 0.88/0.66    inference(resolution,[],[f70,f54])).
% 0.88/0.66  fof(f54,plain,(
% 0.88/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.88/0.66    inference(cnf_transformation,[],[f21])).
% 0.88/0.66  fof(f21,plain,(
% 0.88/0.66    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.88/0.66    inference(ennf_transformation,[],[f10])).
% 0.88/0.66  fof(f10,axiom,(
% 0.88/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.88/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.88/0.66  fof(f110,plain,(
% 0.88/0.66    k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2)),
% 0.88/0.66    inference(global_subsumption,[],[f42,f71,f104])).
% 0.88/0.66  fof(f104,plain,(
% 0.88/0.66    ~v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1) | k1_xboole_0 = sK1 | k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2)),
% 0.88/0.66    inference(resolution,[],[f70,f57])).
% 0.88/0.66  fof(f57,plain,(
% 0.88/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.88/0.66    inference(cnf_transformation,[],[f33])).
% 0.88/0.66  fof(f33,plain,(
% 0.88/0.66    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.88/0.66    inference(nnf_transformation,[],[f25])).
% 0.88/0.66  fof(f25,plain,(
% 0.88/0.66    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.88/0.66    inference(flattening,[],[f24])).
% 0.88/0.66  fof(f24,plain,(
% 0.88/0.66    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.88/0.66    inference(ennf_transformation,[],[f12])).
% 0.88/0.66  fof(f12,axiom,(
% 0.88/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.88/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.88/0.66  fof(f71,plain,(
% 0.88/0.66    v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.88/0.66    inference(definition_unfolding,[],[f40,f69])).
% 0.88/0.66  fof(f40,plain,(
% 0.88/0.66    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.88/0.66    inference(cnf_transformation,[],[f27])).
% 0.88/0.66  fof(f42,plain,(
% 0.88/0.66    k1_xboole_0 != sK1),
% 0.88/0.66    inference(cnf_transformation,[],[f27])).
% 0.88/0.66  fof(f86,plain,(
% 0.88/0.66    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 0.88/0.66    inference(equality_resolution,[],[f85])).
% 0.88/0.66  fof(f85,plain,(
% 0.88/0.66    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 0.88/0.66    inference(equality_resolution,[],[f76])).
% 0.88/0.66  fof(f76,plain,(
% 0.88/0.66    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 0.88/0.66    inference(definition_unfolding,[],[f64,f47])).
% 0.88/0.66  fof(f64,plain,(
% 0.88/0.66    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.88/0.66    inference(cnf_transformation,[],[f38])).
% 0.88/0.66  fof(f38,plain,(
% 0.88/0.66    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.88/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 0.88/0.66  fof(f37,plain,(
% 0.88/0.66    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.88/0.66    introduced(choice_axiom,[])).
% 0.88/0.66  fof(f36,plain,(
% 0.88/0.66    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.88/0.66    inference(rectify,[],[f35])).
% 0.88/0.66  fof(f35,plain,(
% 0.88/0.66    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.88/0.66    inference(flattening,[],[f34])).
% 0.88/0.66  fof(f34,plain,(
% 0.88/0.66    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.88/0.66    inference(nnf_transformation,[],[f2])).
% 0.88/0.66  fof(f2,axiom,(
% 0.88/0.66    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.88/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.88/0.66  fof(f99,plain,(
% 0.88/0.66    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl5_2),
% 0.88/0.66    inference(avatar_component_clause,[],[f98])).
% 0.88/0.66  fof(f98,plain,(
% 0.88/0.66    spl5_2 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.88/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.88/0.66  fof(f117,plain,(
% 0.88/0.66    spl5_4),
% 0.88/0.66    inference(avatar_contradiction_clause,[],[f116])).
% 0.88/0.66  fof(f116,plain,(
% 0.88/0.66    $false | spl5_4),
% 0.88/0.66    inference(resolution,[],[f113,f46])).
% 0.88/0.66  fof(f46,plain,(
% 0.88/0.66    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.88/0.66    inference(cnf_transformation,[],[f7])).
% 0.88/0.66  fof(f7,axiom,(
% 0.88/0.66    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.88/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.88/0.66  fof(f113,plain,(
% 0.88/0.66    ~v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) | spl5_4),
% 0.88/0.66    inference(avatar_component_clause,[],[f112])).
% 0.88/0.66  fof(f112,plain,(
% 0.88/0.66    spl5_4 <=> v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))),
% 0.88/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.88/0.66  fof(f115,plain,(
% 0.88/0.66    ~spl5_4 | spl5_1),
% 0.88/0.66    inference(avatar_split_clause,[],[f109,f95,f112])).
% 0.88/0.66  fof(f95,plain,(
% 0.88/0.66    spl5_1 <=> v1_relat_1(sK2)),
% 0.88/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.88/0.66  fof(f109,plain,(
% 0.88/0.66    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))),
% 0.88/0.66    inference(resolution,[],[f70,f45])).
% 0.88/0.66  fof(f45,plain,(
% 0.88/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.88/0.66    inference(cnf_transformation,[],[f17])).
% 0.88/0.66  fof(f17,plain,(
% 0.88/0.66    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.88/0.66    inference(ennf_transformation,[],[f6])).
% 0.88/0.66  fof(f6,axiom,(
% 0.88/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.88/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.88/0.66  fof(f103,plain,(
% 0.88/0.66    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.88/0.66    inference(avatar_split_clause,[],[f93,f101,f98,f95])).
% 0.88/0.66  fof(f93,plain,(
% 0.88/0.66    ~r1_tarski(k2_relat_1(sK2),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.88/0.66    inference(global_subsumption,[],[f39,f89])).
% 0.88/0.66  fof(f89,plain,(
% 0.88/0.66    ~r1_tarski(k2_relat_1(sK2),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.88/0.66    inference(resolution,[],[f88,f48])).
% 0.88/0.66  fof(f48,plain,(
% 0.88/0.66    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.88/0.66    inference(cnf_transformation,[],[f19])).
% 0.88/0.66  fof(f19,plain,(
% 0.88/0.66    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.88/0.66    inference(flattening,[],[f18])).
% 0.88/0.66  fof(f18,plain,(
% 0.88/0.66    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.88/0.66    inference(ennf_transformation,[],[f8])).
% 0.88/0.66  fof(f8,axiom,(
% 0.88/0.66    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.88/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 0.88/0.66  fof(f88,plain,(
% 0.88/0.66    ( ! [X0] : (~r2_hidden(k1_funct_1(sK2,sK0),X0) | ~r1_tarski(X0,sK1)) )),
% 0.88/0.66    inference(resolution,[],[f43,f49])).
% 0.88/0.66  fof(f49,plain,(
% 0.88/0.66    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.88/0.66    inference(cnf_transformation,[],[f31])).
% 0.88/0.66  fof(f31,plain,(
% 0.88/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.88/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 0.88/0.66  fof(f30,plain,(
% 0.88/0.66    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.88/0.66    introduced(choice_axiom,[])).
% 0.88/0.66  fof(f29,plain,(
% 0.88/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.88/0.66    inference(rectify,[],[f28])).
% 0.88/0.66  fof(f28,plain,(
% 0.88/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.88/0.66    inference(nnf_transformation,[],[f20])).
% 0.88/0.66  fof(f20,plain,(
% 0.88/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.88/0.66    inference(ennf_transformation,[],[f1])).
% 0.88/0.66  fof(f1,axiom,(
% 0.88/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.88/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.88/0.66  fof(f43,plain,(
% 0.88/0.66    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.88/0.66    inference(cnf_transformation,[],[f27])).
% 0.88/0.66  fof(f39,plain,(
% 0.88/0.66    v1_funct_1(sK2)),
% 0.88/0.66    inference(cnf_transformation,[],[f27])).
% 0.88/0.66  % SZS output end Proof for theBenchmark
% 0.88/0.66  % (18491)------------------------------
% 0.88/0.66  % (18491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.88/0.66  % (18491)Termination reason: Refutation
% 0.88/0.66  
% 0.88/0.66  % (18491)Memory used [KB]: 10746
% 0.88/0.66  % (18491)Time elapsed: 0.099 s
% 0.88/0.66  % (18491)------------------------------
% 0.88/0.66  % (18491)------------------------------
% 0.88/0.66  % (18355)Success in time 0.3 s
%------------------------------------------------------------------------------
