%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 214 expanded)
%              Number of leaves         :   20 (  62 expanded)
%              Depth                    :   17
%              Number of atoms          :  314 ( 735 expanded)
%              Number of equality atoms :  134 ( 295 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f139,f159,f167,f175,f195])).

fof(f195,plain,(
    ~ spl7_1 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f193,f83])).

fof(f83,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f193,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f189,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

% (24182)Refutation not found, incomplete strategy% (24182)------------------------------
% (24182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24182)Termination reason: Refutation not found, incomplete strategy

% (24182)Memory used [KB]: 1791
% (24182)Time elapsed: 0.091 s
% (24182)------------------------------
% (24182)------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f189,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl7_1 ),
    inference(superposition,[],[f103,f134])).

fof(f134,plain,
    ( k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl7_1
  <=> k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f103,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f62,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

% (24175)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK6(X0,X1,X2) != X1
              & sK6(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X1
            | sK6(X0,X1,X2) = X0
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).

% (24174)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X1
            & sK6(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X1
          | sK6(X0,X1,X2) = X0
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f175,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f171,f50])).

fof(f50,plain,(
    sK2 != k1_funct_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK2 != k1_funct_1(sK4,sK3)
    & r2_hidden(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK4,sK1,k1_tarski(sK2))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK2 != k1_funct_1(sK4,sK3)
      & r2_hidden(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
      & v1_funct_2(sK4,sK1,k1_tarski(sK2))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f171,plain,
    ( sK2 = k1_funct_1(sK4,sK3)
    | ~ spl7_4 ),
    inference(resolution,[],[f158,f49])).

fof(f49,plain,(
    r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f158,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,sK1)
        | sK2 = k1_funct_1(sK4,X9) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl7_4
  <=> ! [X9] :
        ( ~ r2_hidden(X9,sK1)
        | sK2 = k1_funct_1(sK4,X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f167,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl7_3 ),
    inference(resolution,[],[f165,f86])).

fof(f86,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f48,f85])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f81,f84])).

fof(f81,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f165,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_3 ),
    inference(resolution,[],[f155,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f155,plain,
    ( ~ v1_relat_1(sK4)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl7_3
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f159,plain,
    ( ~ spl7_3
    | spl7_4
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f151,f136,f157,f153])).

fof(f136,plain,
    ( spl7_2
  <=> sK1 = k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f151,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,sK1)
        | sK2 = k1_funct_1(sK4,X9)
        | ~ v1_relat_1(sK4) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f130,f140])).

fof(f140,plain,
    ( sK1 = k1_relat_1(sK4)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f114,f138])).

fof(f138,plain,
    ( sK1 = k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f136])).

fof(f114,plain,(
    k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f86,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f130,plain,(
    ! [X9] :
      ( sK2 = k1_funct_1(sK4,X9)
      | ~ r2_hidden(X9,k1_relat_1(sK4))
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f127,f46])).

fof(f46,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f127,plain,(
    ! [X9] :
      ( sK2 = k1_funct_1(sK4,X9)
      | ~ r2_hidden(X9,k1_relat_1(sK4))
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f123,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f123,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK4))
      | sK2 = X0 ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK4))
      | sK2 = X0
      | sK2 = X0 ) ),
    inference(resolution,[],[f118,f104])).

fof(f104,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f61,f84])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f118,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
      | ~ r2_hidden(X0,k2_relat_1(sK4)) ) ),
    inference(resolution,[],[f117,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f117,plain,(
    m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(subsumption_resolution,[],[f116,f86])).

fof(f116,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(superposition,[],[f77,f113])).

fof(f113,plain,(
    k2_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_relat_1(sK4) ),
    inference(resolution,[],[f86,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f139,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f112,f136,f132])).

fof(f112,plain,
    ( sK1 = k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(global_subsumption,[],[f86,f111])).

fof(f111,plain,
    ( sK1 = k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(resolution,[],[f87,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f87,plain,(
    v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f47,f85])).

fof(f47,plain,(
    v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (24176)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.50  % (24171)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.50  % (24194)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (24178)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (24172)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (24173)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (24180)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (24186)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (24169)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (24168)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (24179)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (24188)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (24190)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (24192)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (24182)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (24189)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (24193)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (24197)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (24192)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (24197)Refutation not found, incomplete strategy% (24197)------------------------------
% 0.21/0.54  % (24197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24197)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24197)Memory used [KB]: 1791
% 0.21/0.54  % (24197)Time elapsed: 0.136 s
% 0.21/0.54  % (24197)------------------------------
% 0.21/0.54  % (24197)------------------------------
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f196,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f139,f159,f167,f175,f195])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    ~spl7_1),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f194])).
% 0.21/0.54  fof(f194,plain,(
% 0.21/0.54    $false | ~spl7_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f193,f83])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f193,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,sK2) | ~spl7_1),
% 0.21/0.54    inference(resolution,[],[f189,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  % (24182)Refutation not found, incomplete strategy% (24182)------------------------------
% 0.21/0.54  % (24182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24182)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24182)Memory used [KB]: 1791
% 0.21/0.54  % (24182)Time elapsed: 0.091 s
% 0.21/0.54  % (24182)------------------------------
% 0.21/0.54  % (24182)------------------------------
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.54  fof(f189,plain,(
% 0.21/0.54    r2_hidden(sK2,k1_xboole_0) | ~spl7_1),
% 0.21/0.54    inference(superposition,[],[f103,f134])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | ~spl7_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f132])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    spl7_1 <=> k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 0.21/0.54    inference(equality_resolution,[],[f102])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 0.21/0.54    inference(equality_resolution,[],[f94])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.21/0.54    inference(definition_unfolding,[],[f62,f84])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f67,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  % (24175)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK6(X0,X1,X2) != X1 & sK6(X0,X1,X2) != X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X1 | sK6(X0,X1,X2) = X0 | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).
% 1.45/0.54  % (24174)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.54  fof(f43,plain,(
% 1.45/0.54    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK6(X0,X1,X2) != X1 & sK6(X0,X1,X2) != X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X1 | sK6(X0,X1,X2) = X0 | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.45/0.54    introduced(choice_axiom,[])).
% 1.45/0.54  fof(f42,plain,(
% 1.45/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.54    inference(rectify,[],[f41])).
% 1.45/0.54  fof(f41,plain,(
% 1.45/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.54    inference(flattening,[],[f40])).
% 1.45/0.54  fof(f40,plain,(
% 1.45/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.54    inference(nnf_transformation,[],[f3])).
% 1.45/0.54  fof(f3,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.45/0.54  fof(f175,plain,(
% 1.45/0.54    ~spl7_4),
% 1.45/0.54    inference(avatar_contradiction_clause,[],[f174])).
% 1.45/0.54  fof(f174,plain,(
% 1.45/0.54    $false | ~spl7_4),
% 1.45/0.54    inference(subsumption_resolution,[],[f171,f50])).
% 1.45/0.54  fof(f50,plain,(
% 1.45/0.54    sK2 != k1_funct_1(sK4,sK3)),
% 1.45/0.54    inference(cnf_transformation,[],[f33])).
% 1.45/0.54  fof(f33,plain,(
% 1.45/0.54    sK2 != k1_funct_1(sK4,sK3) & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4)),
% 1.45/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f32])).
% 1.45/0.54  fof(f32,plain,(
% 1.45/0.54    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK2 != k1_funct_1(sK4,sK3) & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4))),
% 1.45/0.54    introduced(choice_axiom,[])).
% 1.45/0.54  fof(f18,plain,(
% 1.45/0.54    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.45/0.54    inference(flattening,[],[f17])).
% 1.45/0.54  fof(f17,plain,(
% 1.45/0.54    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.45/0.54    inference(ennf_transformation,[],[f16])).
% 1.45/0.54  fof(f16,negated_conjecture,(
% 1.45/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.45/0.54    inference(negated_conjecture,[],[f15])).
% 1.45/0.54  fof(f15,conjecture,(
% 1.45/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 1.45/0.54  fof(f171,plain,(
% 1.45/0.54    sK2 = k1_funct_1(sK4,sK3) | ~spl7_4),
% 1.45/0.54    inference(resolution,[],[f158,f49])).
% 1.45/0.54  fof(f49,plain,(
% 1.45/0.54    r2_hidden(sK3,sK1)),
% 1.45/0.54    inference(cnf_transformation,[],[f33])).
% 1.45/0.54  fof(f158,plain,(
% 1.45/0.54    ( ! [X9] : (~r2_hidden(X9,sK1) | sK2 = k1_funct_1(sK4,X9)) ) | ~spl7_4),
% 1.45/0.54    inference(avatar_component_clause,[],[f157])).
% 1.45/0.54  fof(f157,plain,(
% 1.45/0.54    spl7_4 <=> ! [X9] : (~r2_hidden(X9,sK1) | sK2 = k1_funct_1(sK4,X9))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.45/0.54  fof(f167,plain,(
% 1.45/0.54    spl7_3),
% 1.45/0.54    inference(avatar_contradiction_clause,[],[f166])).
% 1.45/0.54  fof(f166,plain,(
% 1.45/0.54    $false | spl7_3),
% 1.45/0.54    inference(resolution,[],[f165,f86])).
% 1.45/0.54  fof(f86,plain,(
% 1.45/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 1.45/0.54    inference(definition_unfolding,[],[f48,f85])).
% 1.45/0.54  fof(f85,plain,(
% 1.45/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.45/0.54    inference(definition_unfolding,[],[f81,f84])).
% 1.45/0.54  fof(f81,plain,(
% 1.45/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f4])).
% 1.45/0.54  fof(f4,axiom,(
% 1.45/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.45/0.54  fof(f48,plain,(
% 1.45/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 1.45/0.54    inference(cnf_transformation,[],[f33])).
% 1.45/0.54  fof(f165,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_3),
% 1.45/0.54    inference(resolution,[],[f155,f80])).
% 1.45/0.54  fof(f80,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.54    inference(cnf_transformation,[],[f29])).
% 1.45/0.54  fof(f29,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.54    inference(ennf_transformation,[],[f10])).
% 1.45/0.54  fof(f10,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.45/0.54  fof(f155,plain,(
% 1.45/0.54    ~v1_relat_1(sK4) | spl7_3),
% 1.45/0.54    inference(avatar_component_clause,[],[f153])).
% 1.45/0.54  fof(f153,plain,(
% 1.45/0.54    spl7_3 <=> v1_relat_1(sK4)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.45/0.54  fof(f159,plain,(
% 1.45/0.54    ~spl7_3 | spl7_4 | ~spl7_2),
% 1.45/0.54    inference(avatar_split_clause,[],[f151,f136,f157,f153])).
% 1.45/0.54  fof(f136,plain,(
% 1.45/0.54    spl7_2 <=> sK1 = k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.45/0.54  fof(f151,plain,(
% 1.45/0.54    ( ! [X9] : (~r2_hidden(X9,sK1) | sK2 = k1_funct_1(sK4,X9) | ~v1_relat_1(sK4)) ) | ~spl7_2),
% 1.45/0.54    inference(forward_demodulation,[],[f130,f140])).
% 1.45/0.54  fof(f140,plain,(
% 1.45/0.54    sK1 = k1_relat_1(sK4) | ~spl7_2),
% 1.45/0.54    inference(backward_demodulation,[],[f114,f138])).
% 1.45/0.54  fof(f138,plain,(
% 1.45/0.54    sK1 = k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) | ~spl7_2),
% 1.45/0.54    inference(avatar_component_clause,[],[f136])).
% 1.45/0.54  fof(f114,plain,(
% 1.45/0.54    k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_relat_1(sK4)),
% 1.45/0.54    inference(resolution,[],[f86,f78])).
% 1.45/0.54  fof(f78,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f27])).
% 1.45/0.54  fof(f27,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.54    inference(ennf_transformation,[],[f12])).
% 1.45/0.54  fof(f12,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.45/0.54  fof(f130,plain,(
% 1.45/0.54    ( ! [X9] : (sK2 = k1_funct_1(sK4,X9) | ~r2_hidden(X9,k1_relat_1(sK4)) | ~v1_relat_1(sK4)) )),
% 1.45/0.54    inference(subsumption_resolution,[],[f127,f46])).
% 1.45/0.54  fof(f46,plain,(
% 1.45/0.54    v1_funct_1(sK4)),
% 1.45/0.54    inference(cnf_transformation,[],[f33])).
% 1.45/0.54  fof(f127,plain,(
% 1.45/0.54    ( ! [X9] : (sK2 = k1_funct_1(sK4,X9) | ~r2_hidden(X9,k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 1.45/0.54    inference(resolution,[],[f123,f68])).
% 1.45/0.54  fof(f68,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f21])).
% 1.45/0.54  fof(f21,plain,(
% 1.45/0.54    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.45/0.54    inference(flattening,[],[f20])).
% 1.45/0.54  fof(f20,plain,(
% 1.45/0.54    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.45/0.54    inference(ennf_transformation,[],[f8])).
% 1.45/0.54  fof(f8,axiom,(
% 1.45/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 1.45/0.54  fof(f123,plain,(
% 1.45/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK4)) | sK2 = X0) )),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f121])).
% 1.45/0.54  fof(f121,plain,(
% 1.45/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK4)) | sK2 = X0 | sK2 = X0) )),
% 1.45/0.54    inference(resolution,[],[f118,f104])).
% 1.45/0.54  fof(f104,plain,(
% 1.45/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 1.45/0.54    inference(equality_resolution,[],[f95])).
% 1.45/0.54  fof(f95,plain,(
% 1.45/0.54    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.45/0.54    inference(definition_unfolding,[],[f61,f84])).
% 1.45/0.54  fof(f61,plain,(
% 1.45/0.54    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.45/0.54    inference(cnf_transformation,[],[f44])).
% 1.45/0.54  fof(f118,plain,(
% 1.45/0.54    ( ! [X0] : (r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) | ~r2_hidden(X0,k2_relat_1(sK4))) )),
% 1.45/0.54    inference(resolution,[],[f117,f70])).
% 1.45/0.54  fof(f70,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f23])).
% 1.45/0.54  fof(f23,plain,(
% 1.45/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f7])).
% 1.45/0.54  fof(f7,axiom,(
% 1.45/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.45/0.54  fof(f117,plain,(
% 1.45/0.54    m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2)))),
% 1.45/0.54    inference(subsumption_resolution,[],[f116,f86])).
% 1.45/0.54  fof(f116,plain,(
% 1.45/0.54    m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 1.45/0.54    inference(superposition,[],[f77,f113])).
% 1.45/0.54  fof(f113,plain,(
% 1.45/0.54    k2_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_relat_1(sK4)),
% 1.45/0.54    inference(resolution,[],[f86,f79])).
% 1.45/0.54  fof(f79,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f28])).
% 1.45/0.54  fof(f28,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.54    inference(ennf_transformation,[],[f13])).
% 1.45/0.54  fof(f13,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.45/0.54  fof(f77,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.54    inference(cnf_transformation,[],[f26])).
% 1.45/0.54  fof(f26,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.54    inference(ennf_transformation,[],[f11])).
% 1.45/0.54  fof(f11,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.45/0.54  fof(f139,plain,(
% 1.45/0.54    spl7_1 | spl7_2),
% 1.45/0.54    inference(avatar_split_clause,[],[f112,f136,f132])).
% 1.45/0.54  fof(f112,plain,(
% 1.45/0.54    sK1 = k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)),
% 1.45/0.54    inference(global_subsumption,[],[f86,f111])).
% 1.45/0.54  fof(f111,plain,(
% 1.45/0.54    sK1 = k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 1.45/0.54    inference(resolution,[],[f87,f71])).
% 1.45/0.54  fof(f71,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.54    inference(cnf_transformation,[],[f45])).
% 1.45/0.54  fof(f45,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.54    inference(nnf_transformation,[],[f25])).
% 1.45/0.54  fof(f25,plain,(
% 1.45/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.54    inference(flattening,[],[f24])).
% 1.45/0.54  fof(f24,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.54    inference(ennf_transformation,[],[f14])).
% 1.45/0.54  fof(f14,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.45/0.54  fof(f87,plain,(
% 1.45/0.54    v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2))),
% 1.45/0.54    inference(definition_unfolding,[],[f47,f85])).
% 1.45/0.54  fof(f47,plain,(
% 1.45/0.54    v1_funct_2(sK4,sK1,k1_tarski(sK2))),
% 1.45/0.54    inference(cnf_transformation,[],[f33])).
% 1.45/0.54  % SZS output end Proof for theBenchmark
% 1.45/0.54  % (24177)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.45/0.54  % (24187)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.45/0.54  % (24181)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.45/0.54  % (24195)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.45/0.55  % (24185)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.45/0.55  % (24170)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.45/0.55  % (24192)------------------------------
% 1.45/0.55  % (24192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (24192)Termination reason: Refutation
% 1.45/0.55  
% 1.45/0.55  % (24192)Memory used [KB]: 10746
% 1.45/0.55  % (24192)Time elapsed: 0.130 s
% 1.45/0.55  % (24192)------------------------------
% 1.45/0.55  % (24192)------------------------------
% 1.45/0.55  % (24167)Success in time 0.193 s
%------------------------------------------------------------------------------
