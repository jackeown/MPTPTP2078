%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 250 expanded)
%              Number of leaves         :   33 ( 101 expanded)
%              Depth                    :   14
%              Number of atoms          :  434 ( 796 expanded)
%              Number of equality atoms :   81 ( 133 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f245,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f76,f78,f82,f87,f97,f102,f105,f132,f135,f146,f152,f158,f163,f168,f174,f187,f205,f231,f237])).

fof(f237,plain,
    ( spl3_20
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f233,f229,f203])).

fof(f203,plain,
    ( spl3_20
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f229,plain,
    ( spl3_23
  <=> ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(sK1,k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f233,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl3_23 ),
    inference(resolution,[],[f232,f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f39,f38])).

fof(f38,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f232,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
        | v1_funct_2(sK1,k1_xboole_0,X0) )
    | ~ spl3_23 ),
    inference(resolution,[],[f230,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f230,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(sK1,k1_xboole_0,X0) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f229])).

fof(f231,plain,
    ( ~ spl3_5
    | spl3_23
    | ~ spl3_7
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f227,f185,f172,f92,f229,f80])).

fof(f80,plain,
    ( spl3_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f92,plain,
    ( spl3_7
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f172,plain,
    ( spl3_17
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f185,plain,
    ( spl3_18
  <=> k1_xboole_0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
        | ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(sK1,k1_xboole_0,X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f226,f186])).

fof(f186,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f185])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(sK1,k1_xboole_0,X0)
        | ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f224,f173])).

fof(f173,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f172])).

fof(f224,plain,
    ( ! [X0] :
        ( v1_funct_2(sK1,k1_xboole_0,X0)
        | ~ r1_tarski(k2_relat_1(sK1),X0)
        | ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_18 ),
    inference(resolution,[],[f195,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f195,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
        | v1_funct_2(sK1,k1_xboole_0,X5) )
    | ~ spl3_18 ),
    inference(trivial_inequality_removal,[],[f192])).

fof(f192,plain,
    ( ! [X5] :
        ( k1_xboole_0 != k1_xboole_0
        | v1_funct_2(sK1,k1_xboole_0,X5)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) )
    | ~ spl3_18 ),
    inference(superposition,[],[f113,f186])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f61,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f61,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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

fof(f205,plain,
    ( ~ spl3_20
    | spl3_15
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f201,f185,f161,f203])).

fof(f161,plain,
    ( spl3_15
  <=> v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f201,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | spl3_15
    | ~ spl3_18 ),
    inference(superposition,[],[f162,f186])).

fof(f162,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f161])).

fof(f187,plain,
    ( ~ spl3_5
    | spl3_18
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f179,f172,f185,f80])).

fof(f179,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_17 ),
    inference(trivial_inequality_removal,[],[f178])).

fof(f178,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_17 ),
    inference(superposition,[],[f43,f173])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

% (13159)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f174,plain,
    ( spl3_17
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f170,f166,f95,f172])).

fof(f95,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f166,plain,
    ( spl3_16
  <=> r1_tarski(k2_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f170,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(resolution,[],[f167,f108])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl3_8 ),
    inference(resolution,[],[f106,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl3_8 ),
    inference(resolution,[],[f96,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f167,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f166])).

fof(f168,plain,
    ( spl3_16
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f164,f143,f74,f166])).

fof(f74,plain,
    ( spl3_4
  <=> r1_tarski(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f143,plain,
    ( spl3_13
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f164,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(superposition,[],[f75,f144])).

fof(f144,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f75,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f163,plain,
    ( ~ spl3_15
    | spl3_2
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f159,f143,f67,f161])).

fof(f67,plain,
    ( spl3_2
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f159,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl3_2
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f68,f144])).

fof(f68,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f158,plain,
    ( ~ spl3_10
    | spl3_12 ),
    inference(avatar_split_clause,[],[f157,f137,f127])).

fof(f127,plain,
    ( spl3_10
  <=> m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f137,plain,
    ( spl3_12
  <=> r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f157,plain,
    ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_relat_1(sK1)))
    | spl3_12 ),
    inference(resolution,[],[f138,f46])).

fof(f138,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f152,plain,
    ( ~ spl3_5
    | ~ spl3_12
    | ~ spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f148,f70,f74,f137,f80])).

fof(f70,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f148,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),sK0)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl3_3 ),
    inference(resolution,[],[f71,f48])).

fof(f71,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f146,plain,
    ( spl3_13
    | spl3_2
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f140,f130,f74,f67,f143])).

fof(f130,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK1),X0)
        | v1_funct_2(sK1,k1_relat_1(sK1),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f140,plain,
    ( v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | k1_xboole_0 = sK0
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(resolution,[],[f131,f75])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK1),X0)
        | v1_funct_2(sK1,k1_relat_1(sK1),X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f130])).

fof(f135,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f128,f83])).

fof(f128,plain,
    ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_relat_1(sK1)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f132,plain,
    ( ~ spl3_10
    | spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f125,f80,f130,f127])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK1),X0)
        | k1_xboole_0 = X0
        | v1_funct_2(sK1,k1_relat_1(sK1),X0)
        | ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_relat_1(sK1))) )
    | ~ spl3_5 ),
    inference(resolution,[],[f124,f81])).

fof(f81,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1)
      | k1_xboole_0 = X1
      | v1_funct_2(X0,k1_relat_1(X0),X1)
      | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_relat_1(X0))) ) ),
    inference(resolution,[],[f121,f46])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X1))
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f120,f48])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
      | k1_xboole_0 = X1
      | v1_funct_2(X0,k1_relat_1(X0),X1) ) ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f52,f49])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f105,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f101,f83])).

fof(f101,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f100])).

% (13169)Refutation not found, incomplete strategy% (13169)------------------------------
% (13169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13169)Termination reason: Refutation not found, incomplete strategy

% (13169)Memory used [KB]: 10618
% (13169)Time elapsed: 0.070 s
% (13169)------------------------------
% (13169)------------------------------
fof(f100,plain,
    ( spl3_9
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f102,plain,
    ( ~ spl3_9
    | spl3_7 ),
    inference(avatar_split_clause,[],[f98,f92,f100])).

fof(f98,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl3_7 ),
    inference(resolution,[],[f93,f46])).

fof(f93,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f97,plain,
    ( ~ spl3_7
    | spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f90,f85,f95,f92])).

fof(f85,plain,
    ( spl3_6
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl3_6 ),
    inference(resolution,[],[f89,f86])).

fof(f86,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X1,X3)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X1,X3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f56,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f87,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f57,f85])).

fof(f57,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f82,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f34,f80])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
        | ~ v1_funct_1(sK1) )
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f78,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f35,f64])).

fof(f64,plain,
    ( spl3_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f36,f74])).

fof(f36,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f37,f70,f67,f64])).

fof(f37,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:09:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (13164)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (13173)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (13163)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (13160)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (13173)Refutation not found, incomplete strategy% (13173)------------------------------
% 0.21/0.48  % (13173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (13173)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (13173)Memory used [KB]: 6140
% 0.21/0.48  % (13173)Time elapsed: 0.030 s
% 0.21/0.48  % (13173)------------------------------
% 0.21/0.48  % (13173)------------------------------
% 0.21/0.48  % (13161)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (13169)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (13164)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f72,f76,f78,f82,f87,f97,f102,f105,f132,f135,f146,f152,f158,f163,f168,f174,f187,f205,f231,f237])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    spl3_20 | ~spl3_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f233,f229,f203])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    spl3_20 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    spl3_23 <=> ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(sK1,k1_xboole_0,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~spl3_23),
% 0.21/0.49    inference(resolution,[],[f232,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f39,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | v1_funct_2(sK1,k1_xboole_0,X0)) ) | ~spl3_23),
% 0.21/0.49    inference(resolution,[],[f230,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(sK1,k1_xboole_0,X0)) ) | ~spl3_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f229])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    ~spl3_5 | spl3_23 | ~spl3_7 | ~spl3_17 | ~spl3_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f227,f185,f172,f92,f229,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl3_5 <=> v1_relat_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl3_7 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    spl3_17 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    spl3_18 <=> k1_xboole_0 = k1_relat_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X0) | v1_funct_2(sK1,k1_xboole_0,X0) | ~v1_relat_1(sK1)) ) | (~spl3_17 | ~spl3_18)),
% 0.21/0.49    inference(forward_demodulation,[],[f226,f186])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(sK1) | ~spl3_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f185])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(sK1,k1_xboole_0,X0) | ~r1_tarski(k1_relat_1(sK1),k1_xboole_0) | ~v1_relat_1(sK1)) ) | (~spl3_17 | ~spl3_18)),
% 0.21/0.49    inference(forward_demodulation,[],[f224,f173])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(sK1) | ~spl3_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f172])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_2(sK1,k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(sK1),X0) | ~r1_tarski(k1_relat_1(sK1),k1_xboole_0) | ~v1_relat_1(sK1)) ) | ~spl3_18),
% 0.21/0.49    inference(resolution,[],[f195,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    ( ! [X5] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) | v1_funct_2(sK1,k1_xboole_0,X5)) ) | ~spl3_18),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f192])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    ( ! [X5] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(sK1,k1_xboole_0,X5) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))) ) | ~spl3_18),
% 0.21/0.49    inference(superposition,[],[f113,f186])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f112])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.21/0.49    inference(superposition,[],[f61,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.49    inference(equality_resolution,[],[f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    ~spl3_20 | spl3_15 | ~spl3_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f201,f185,f161,f203])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    spl3_15 <=> v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (spl3_15 | ~spl3_18)),
% 0.21/0.49    inference(superposition,[],[f162,f186])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | spl3_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f161])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    ~spl3_5 | spl3_18 | ~spl3_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f179,f172,f185,f80])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(sK1) | ~v1_relat_1(sK1) | ~spl3_17),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f178])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(sK1) | ~v1_relat_1(sK1) | ~spl3_17),
% 0.21/0.49    inference(superposition,[],[f43,f173])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.49  % (13159)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    spl3_17 | ~spl3_8 | ~spl3_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f170,f166,f95,f172])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl3_8 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    spl3_16 <=> r1_tarski(k2_relat_1(sK1),k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(sK1) | (~spl3_8 | ~spl3_16)),
% 0.21/0.49    inference(resolution,[],[f167,f108])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl3_8),
% 0.21/0.49    inference(resolution,[],[f106,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl3_8),
% 0.21/0.49    inference(resolution,[],[f96,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) ) | ~spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f95])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK1),k1_xboole_0) | ~spl3_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f166])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    spl3_16 | ~spl3_4 | ~spl3_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f164,f143,f74,f166])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    spl3_4 <=> r1_tarski(k2_relat_1(sK1),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    spl3_13 <=> k1_xboole_0 = sK0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK1),k1_xboole_0) | (~spl3_4 | ~spl3_13)),
% 0.21/0.49    inference(superposition,[],[f75,f144])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | ~spl3_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f143])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK1),sK0) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f74])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ~spl3_15 | spl3_2 | ~spl3_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f159,f143,f67,f161])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl3_2 <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | (spl3_2 | ~spl3_13)),
% 0.21/0.49    inference(forward_demodulation,[],[f68,f144])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ~spl3_10 | spl3_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f157,f137,f127])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    spl3_10 <=> m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_relat_1(sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl3_12 <=> r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_relat_1(sK1))) | spl3_12),
% 0.21/0.49    inference(resolution,[],[f138,f46])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | spl3_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f137])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ~spl3_5 | ~spl3_12 | ~spl3_4 | spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f148,f70,f74,f137,f80])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK1),sK0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | spl3_3),
% 0.21/0.49    inference(resolution,[],[f71,f48])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f70])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    spl3_13 | spl3_2 | ~spl3_4 | ~spl3_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f140,f130,f74,f67,f143])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    spl3_11 <=> ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | v1_funct_2(sK1,k1_relat_1(sK1),X0) | k1_xboole_0 = X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    v1_funct_2(sK1,k1_relat_1(sK1),sK0) | k1_xboole_0 = sK0 | (~spl3_4 | ~spl3_11)),
% 0.21/0.49    inference(resolution,[],[f131,f75])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | v1_funct_2(sK1,k1_relat_1(sK1),X0) | k1_xboole_0 = X0) ) | ~spl3_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f130])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    spl3_10),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f133])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    $false | spl3_10),
% 0.21/0.49    inference(resolution,[],[f128,f83])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_relat_1(sK1))) | spl3_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f127])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ~spl3_10 | spl3_11 | ~spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f125,f80,f130,f127])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | k1_xboole_0 = X0 | v1_funct_2(sK1,k1_relat_1(sK1),X0) | ~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_relat_1(sK1)))) ) | ~spl3_5),
% 0.21/0.49    inference(resolution,[],[f124,f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    v1_relat_1(sK1) | ~spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f80])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1) | k1_xboole_0 = X1 | v1_funct_2(X0,k1_relat_1(X0),X1) | ~m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_relat_1(X0)))) )),
% 0.21/0.49    inference(resolution,[],[f121,f46])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),k1_relat_1(X1)) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(resolution,[],[f120,f48])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) | k1_xboole_0 = X1 | v1_funct_2(X0,k1_relat_1(X0),X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f119])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f118])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(superposition,[],[f52,f49])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    spl3_9),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f103])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    $false | spl3_9),
% 0.21/0.49    inference(resolution,[],[f101,f83])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f100])).
% 0.21/0.49  % (13169)Refutation not found, incomplete strategy% (13169)------------------------------
% 0.21/0.49  % (13169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13169)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (13169)Memory used [KB]: 10618
% 0.21/0.49  % (13169)Time elapsed: 0.070 s
% 0.21/0.49  % (13169)------------------------------
% 0.21/0.49  % (13169)------------------------------
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl3_9 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ~spl3_9 | spl3_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f98,f92,f100])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl3_7),
% 0.21/0.49    inference(resolution,[],[f93,f46])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f92])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ~spl3_7 | spl3_8 | ~spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f90,f85,f95,f92])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl3_6 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) ) | ~spl3_6),
% 0.21/0.49    inference(resolution,[],[f89,f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f85])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X0) | ~r1_tarski(X1,X3) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(resolution,[],[f56,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f57,f85])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    inference(equality_resolution,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f80])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f12])).
% 0.21/0.49  fof(f12,conjecture,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f35,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl3_1 <=> v1_funct_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    v1_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f36,f74])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f70,f67,f64])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (13164)------------------------------
% 0.21/0.49  % (13164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13164)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (13164)Memory used [KB]: 10746
% 0.21/0.49  % (13164)Time elapsed: 0.012 s
% 0.21/0.49  % (13164)------------------------------
% 0.21/0.49  % (13164)------------------------------
% 0.21/0.49  % (13159)Refutation not found, incomplete strategy% (13159)------------------------------
% 0.21/0.49  % (13159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13159)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (13159)Memory used [KB]: 10618
% 0.21/0.49  % (13159)Time elapsed: 0.081 s
% 0.21/0.49  % (13159)------------------------------
% 0.21/0.49  % (13159)------------------------------
% 0.21/0.49  % (13157)Success in time 0.132 s
%------------------------------------------------------------------------------
